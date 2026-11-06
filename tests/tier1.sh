#!/usr/bin/env bash
# Tier 1: the build (warnings are errors) and no `sorry`. Run under the Lean toolchain (mise exec -- tests/tier1.sh). The axiom check joins with the first theorem.
set -euo pipefail
cd "$(dirname "$0")/.."
lake build
! grep -rnw 'sorry' VbmJournal VbmJournalProofs --include='*.lean' || { echo "tier1: sorry found" >&2; exit 1; }
echo "ran: tier1: build and sorry check"
