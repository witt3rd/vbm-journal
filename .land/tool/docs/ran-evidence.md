# Ran-evidence: a check that never ran must not pass

The defect class (first seen in a downstream repository's zero-warning self-test): a negative self-test passes when the thing under test never ran. A guard that refuses a tool, a skipped
check or an early exit makes a check report success without running it.

The format every test script prints on success, and the one line `tests/run.sh` accepts as proof that the script executed something:

    ran: NAME: N cases              NAME = [A-Za-z0-9_.-]+, N = a positive integer (the checks that were evaluated and held)

`tests/lib.sh` `finish` prints it (N = the passed checks) and fails when no check ran or one failed. `tests/run.sh` fails a script that exits 0 without a valid line, with a sum of zero, or with a
`SKIPPED` line, and prints `ran: tests: N cases` for the batch. Shared negative tests: `tests/test_harness.sh` (a script that ran no check fails; a refused tool, exit 126, is not a pass) and
`tests/test_runner.sh` (the runner fails a script with no, zero or skipped evidence and names it).

Honest weakness: a count proves a count was printed, not that every case was meaningful; and the number is the checks evaluated, not coverage.

## Where the code lives

The pair is part of the payload every repository vendors: `lib/ran.sh` (sourced by a test script: `ran_case` counts an executed case, `ran_done NAME` prints the evidence line and fails when no case ran, `must_fail` is a negative
self-test that a refusal, a missing tool or a timeout cannot satisfy) and `bin/ran-evidence` (the reader: `check NAME LOG`, `gate NAME REGEX CMD...`, `check-dir DIR MAP`). A repository carries no copy of either. Both are tested
in `tests/test_ran.sh` against every shape of "it did not run", each with a control that passes; `tests/run.sh` of this repository uses the same reader.

