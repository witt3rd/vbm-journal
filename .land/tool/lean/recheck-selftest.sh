#!/usr/bin/env bash
# The negative test of `land-lean recheck` (docs/lean-gates.md): the checker must ACCEPT a true theorem and REJECT a false one that was added to the environment with the kernel check skipped (what an unsound
# kernel would let through). Run with the toolchain on PATH (`lake env`), from anywhere; $1 is the checker command. A checker that accepts everything proves nothing, and this is what finds it.
set -euo pipefail
checker=${1:-leanchecker}
d=$(mktemp -d "${TMPDIR:-/tmp}/recheck-selftest.XXXXXX"); trap 'rm -rf "$d"' EXIT; mkdir -p "$d/out"; cd "$d"
printf 'theorem fine : (1 : Nat) = 1 := rfl\n' > Good.lean
cat > Lie.lean <<'LEAN'
import Lean
open Lean Elab Command
set_option debug.skipKernelTC true in
run_cmd liftCoreM <| addDecl (.thmDecl { name := `lie, levelParams := [], type := mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) (mkRawNatLit 1) (mkRawNatLit 2), value := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkRawNatLit 1) })
LEAN
for m in Good Lie; do lean "$m.lean" -o "out/$m.olean" >/dev/null 2>&1 || { echo "recheck self-test: could not compile $m (the toolchain on PATH?)" >&2; exit 1; }; done
export LEAN_PATH="$d/out:$(lean --print-libdir)"
"$checker" --fresh Good >/dev/null 2>&1 || { echo "recheck self-test FAILED: the checker rejected a true theorem" >&2; exit 1; }
if "$checker" --fresh Lie >/dev/null 2>&1; then echo "recheck self-test FAILED: the checker accepted the false theorem (a gate that cannot reject proves nothing)" >&2; exit 1; fi
echo "recheck self-test ok (a true theorem is accepted, a false one added with the kernel check skipped is rejected)"
