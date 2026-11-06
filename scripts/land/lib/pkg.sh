#!/usr/bin/env bash
# Pinned PACKAGES: a second signed source (the first: vbm-gates) vendored into scripts/<name>/ exactly like this tool is vendored into scripts/land/. Sourced, never run.
# A package source is a repository with MANIFEST.sha256 (`<sha256>  <path>` per file), VERSION, and signed annotated release tags that record the manifest hash (what bin/land-release makes).
# Everything the manifest lists lands in scripts/<name>/<path>; the consumer's variation is scripts/<name>.conf (known keys only, land-check) and nothing else. A file is executable
# iff it starts with `#!` (the mode is a function of the content, so the signed manifest covers it and the offline check can verify it).

pkg_name_ok() { [[ "$1" =~ ^[a-z][a-z0-9-]{0,30}$ ]] && [ "$1" != land ]; }
pkg_path_ok() { [[ "$1" =~ ^[A-Za-z0-9_@+][A-Za-z0-9_./@+-]*$ && "/$1/" != *"/../"* && "/$1/" != *"/./"* && "$1" != */ && "$1" != *//* && "$1" != PIN && "$1" != MANIFEST.sha256 ]]; }
pkg_is_exec() { [ "$(head -c2 -- "$1" 2>/dev/null || true)" = '#!' ]; }

# pkg_install ROOT NAME SRC COMMIT TREE MANIFEST SIGNATURE: every listed file is checked against its hash in TREE (an archive of COMMIT) and its path is a plain relative one, BEFORE anything is written;
# then scripts/<name>/ is replaced by the release and its PIN written. Nothing of the package runs.
pkg_install() {
  local root=$1 pkg=$2 src=$3 commit=$4 tree=$5 man=$6 sig=$7 d h f
  while read -r h f; do [ -n "$f" ] || continue
    pkg_path_ok "$f" || { echo "pkg: $f is not a plain relative path a package may install (nothing was written)" >&2; return 1; }
    [ -f "$tree/$f" ] && [ ! -L "$tree/$f" ] && [ "$(sha256sum < "$tree/$f" | cut -d' ' -f1)" = "$h" ] || { echo "pkg: $f does not match its manifest entry: refusing (nothing was written)" >&2; return 1; }
  done < "$man"
  [ -r "$tree/VERSION" ] || { echo "pkg: the release has no VERSION file" >&2; return 1; }
  d=$root/scripts/$pkg; rm -rf "$d"; mkdir -p "$d"
  while read -r h f; do [ -n "$f" ] || continue
    mkdir -p "$d/$(dirname "$f")"; cp "$tree/$f" "$d/$f"; if pkg_is_exec "$d/$f"; then chmod +x "$d/$f"; else chmod -x "$d/$f"; fi
  done < "$man"
  cp "$man" "$d/MANIFEST.sha256"
  printf 'source=%s\nversion=v%s\ncommit=%s\nmanifest_sha256=%s\nsignature=%s\n' "$src" "$(cat "$tree/VERSION")" "$commit" "$(sha256sum < "$man" | cut -d' ' -f1)" "$sig" > "$d/PIN"
}

# pkgconf_load NAME CONF KEYS: the repository's variation of package NAME, DATA like land.conf: CONF (scripts/NAME.conf; absent = defaults) holds `NAME_KEY=value` lines (NAME upper case, - as _), `#` comments, one pair of quotes
# around a value, nothing expanded or run. Every key must be listed in KEYS (the package's own list, one per line, `#` comments, in the pinned copy: scripts/NAME/KEYS): an UNKNOWN KEY FAILS (a typo must not silently turn a
# gate off). Sets the variables. Returns 2 with a message otherwise. A package reads its configuration through this function (. scripts/land/lib/pkg.sh) so the check and the reader cannot disagree.
pkgconf_load() {
  local pkg=$1 conf=$2 keys=$3 up line n=0 k v known
  [ -r "$conf" ] || return 0
  up=$(printf '%s' "$pkg" | tr 'a-z-' 'A-Z_'); known=" $(sed 's/#.*//' "$keys" 2>/dev/null | tr -s '[:space:]' ' ') "
  while IFS= read -r line || [ -n "$line" ]; do
    n=$((n + 1)); line=${line%$'\r'}
    [[ "$line" =~ ^[[:space:]]*(#.*)?$ ]] && continue
    [[ "$line" =~ ^[[:space:]]*(${up}_[A-Z0-9_]+)=(.*)$ ]] || { echo "scripts/$pkg.conf:$n: not a ${up}_KEY=value line: $line" >&2; return 2; }
    k=${BASH_REMATCH[1]}; v=${BASH_REMATCH[2]}
    case "$known" in *" $k "*) ;; *) echo "scripts/$pkg.conf:$n: unknown key $k (not in scripts/$pkg/KEYS: a typo would silently turn a gate off)" >&2; return 2;; esac
    v=${v%"${v##*[![:space:]]}"}; if [[ "$v" =~ ^\"(.*)\"$ ]] || [[ "$v" =~ ^\'(.*)\'$ ]]; then v=${BASH_REMATCH[1]}; fi
    printf -v "$k" '%s' "$v"
  done < "$conf"
  return 0
}
