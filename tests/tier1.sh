#!/usr/bin/env bash
# Tier 1: the build (warnings are errors; the C of the shims is compiled and linked into the test program) and no `sorry`; the differential test of the driver over the real shims against the model; the real crash test. Run under the Lean toolchain (mise exec -- tests/tier1.sh).
set -euo pipefail
cd "$(dirname "$0")/.."
lake build
! grep -rnw 'sorry' VbmJournal VbmJournalProofs --include='*.lean' || { echo "tier1: sorry found" >&2; exit 1; }
.lake/build/bin/vbm-journal-test
tests/crash.sh
.land/tool/bin/land-lean trust   # the trust ledger (docs/trust-ledger.md): what cannot be proven is marked as trusted, and what must be marked is derived from the tree (vbm-land docs/lean-gates.md)
echo "ran: tier1: build, sorry check, differential test, crash test, trust ledger"
