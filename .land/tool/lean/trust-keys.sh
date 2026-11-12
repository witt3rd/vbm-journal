#!/usr/bin/env bash
# lean/trust-keys.sh: prints the keys the trust ledger MUST cover, derived from the tree and .land/lean.conf (docs/lean-gates.md). Run by `land-lean trust` from the repository root with the configuration exported.
# The tool decides WHAT is required; the configuration says WHERE to look. A file not yet added to git is still required.
set -euo pipefail
files() { git ls-files --cached --others --exclude-standard -- "$@"; }
{
  # the build pins and the configured trusted files (C, loaders, workflows)
  { set -f; files lean-toolchain mise.toml lakefile.lean lakefile.toml $LAND_LEAN_TRUST_FILES; } | sed 's/^/file:/'   # set -f: the configured values are git pathspecs, the shell must not expand them (the pipeline's own subshell keeps it from leaking)
  # what the Lean pin brings: the compiler (frontend, kernel, C emitter), the runtime (lean.h, libleanrt), the bundled clang and ld.lld
  [ ! -f lean-toolchain ] || printf '%s\n' lean-compiler lean-runtime clang-lld
  # every FFI symbol declared in the configured source directories (an unnamed one needs a key too)
  for d in $LAND_LEAN_TRUST_EXTERN_DIRS; do [ -d "$d" ] || continue
    grep -rhE '^[[:space:]]*@\[extern' "$d" --include='*.lean' --exclude-dir=.lake --exclude-dir=vendor 2>/dev/null | sed -E 's/.*@\[extern[^"]*"([^"]+)".*/extern:\1/; t; s/.*/extern:UNNAMED/' || true; done
  # every vendored library is a ledger line (pin:NAME, from the lock); and what any vendored library carries, however deep it is vendored (a library inside a vendored library runs in our artifacts all the same), is
  # trusted code: its C headers (dep:NAME/include/F.h) and the @[extern] symbols its Lean sources declare
  [ ! -f .land/pins.lock ] || awk '!/^#/ && NF {print "pin:" $1}' .land/pins.lock
  if [ -d vendor ]; then
    # each library's own include/*.h (its published surface, what a consumer compiles against), named by the library: a library is any directory directly under a directory named vendor, at any depth
    find vendor \( -name .lake -o -name .git \) -prune -o -type d -name vendor -print | while IFS= read -r v; do
      for d in "$v"/*/; do [ -d "$d" ] || continue; n=$(basename "$d"); for h in "$d"include/*.h; do [ -f "$h" ] && echo "dep:$n/include/$(basename "$h")" || true; done; done; done
    grep -rhE '^[[:space:]]*@\[extern' vendor --include='*.lean' --exclude-dir=.lake --exclude-dir=tests 2>/dev/null | sed -E 's/.*@\[extern[^"]*"([^"]+)".*/extern:\1/; t; s/.*/extern:UNNAMED/' || true
  fi
  # the checker runs in Python, so python3 is always a trusted tool; the others are a watch-list found in the scripts and the build file
  echo tool:python3
  for t in $LAND_LEAN_TRUST_TOOLS; do
    files scripts lakefile.lean lakefile.toml | xargs grep -lw -- "$t" >/dev/null 2>&1 && echo "tool:$t" || true; done
  # what the tool cannot derive (for instance the closure modules that are neither spec nor toolchain): a command of the repository's, one key per line
  [ -z "$LAND_LEAN_TRUST_KEYS_CMD" ] || bash -c "$LAND_LEAN_TRUST_KEYS_CMD"
} | sort -u
