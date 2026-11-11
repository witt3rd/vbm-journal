#!/usr/bin/env bash
# Where the upstream copy of this tool lives, and how to look at it at one exact commit. Sourced, never run.
#   src_fetch SRC REF DEST   makes DEST a bare clone of SRC (OWNER/NAME on GitHub: an ANONYMOUS https clone first, so a public source needs no token, no `gh` login and no secret; only when that fails, `gh`, for a private source;
#   or anything git can clone: a URL or a path) and prints the 40-hex commit REF names. VBM_LAND_URL_BASE replaces https://github.com (the tests serve a local copy).
. "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/paths.sh"   # every consumer path, defined once (lib/paths.sh)
. "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/verify.sh"   # the one verifier: src_verify, src_check_tag, tree_hash (lib/verify.sh)

src_fetch() {
  local src=$1 ref=$2 dest=$3 c
  if [[ "$src" =~ ^[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+$ ]] && [ ! -e "$src" ]; then
    GIT_TERMINAL_PROMPT=0 GIT_ASKPASS=true timeout 120 git -c credential.helper= clone -q --bare -- "${VBM_LAND_URL_BASE:-https://github.com}/$src.git" "$dest" >/dev/null 2>&1 || { rm -rf "$dest"
      "${GH:-gh}" repo clone "$src" "$dest" -- --quiet --bare >/dev/null 2>&1 || { echo "cannot clone $src (anonymously over https, nor with gh: a private source needs a read token in GH_TOKEN)" >&2; return 1; }; }
  else
    git clone -q --bare -- "$src" "$dest" >/dev/null 2>&1 || { echo "cannot clone $src" >&2; return 1; }
  fi
  c=$(git -C "$dest" rev-parse --verify -q "$ref^{commit}") || { echo "$src has no such tag or commit: $ref" >&2; return 1; }
  [[ "$c" =~ ^[0-9a-f]{40}$ ]] || return 1
  printf '%s\n' "$c"
}
