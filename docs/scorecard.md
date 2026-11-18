# Scorecard

Status: draft by a worker, 2026-11-18; goals and targets are the owner's to set.

How well vbm-journal is doing against its own goals, as the repository states them. A steward uses it to judge health, measure progress and set priorities. The floor only moves toward better: when `now` beats it, the floor takes the new value; a landing that makes a metric worse than its floor is a regression. All metrics are integers; the unit is in the name. History is at the end (one line per measurement).

## Goals as the repository states them

1. **A verified journal: the specification as a Lean model with proofs, and the verified implementation over a minimal write+fsync shim.** `README.md:2`; the theorem families (append-only, chain integrity, crash consistency, fencing, recovery) `docs/slice1.md:20`-`docs/slice1.md:26`; the implementation proved equal to the model `docs/slice2.md:3`, `docs/slice2.md:37`.
2. **The proofs rest on the standard axioms only, with no `sorry`; the build fails otherwise.** `docs/slice1.md:28`, `docs/slice3.md:50`, `VbmJournalProofs/Axioms.lean:11`.
3. **Only one file is trusted code (`native/vbm_journal.c`, 170 lines, 148 of code); everything else is Lean and proved; every trusted thing has a ledger entry with its contract and a test.** `docs/trust-ledger.md:3`, `docs/trust-ledger.md:5` (entry format), `docs/slice2.md:3`.
4. **Proofs, not tests: a test exists only for the boundary the proofs do not cover** (the shims against their models, the real crash test). `AGENTS.md:11`, `tests/tier1.sh:2`.
5. **Consumable by a host that keeps JSON lines, with the proofs intact, over journals of megabytes** (the flat reader; no per-line recursion). `README.md:2`, `docs/slice3.md:1`, `docs/slice3.md:7`. Speed is measured, not proved, and not a gate: `docs/slice3.md:58`.
6. **Landed directly with vbm-land; Tier 1 is the build, the proofs and the axiom, sorry and new-C checks; the pinned tool is never edited; a landing must not add a failure.** `README.md:2`, `AGENTS.md:6`, `AGENTS.md:5`, `AGENTS.md:2` (small diffs, no long red).

## Metrics

Commands run from the repository root, with the Lean toolchain on `PATH` (`mise exec -- CMD` when mise can reach the network). In the table `\|` is a markdown escape for a pipe: type `|`. `now` was measured 2026-11-18 on mcfeely (4 cores, 31 GB, shared) with Lean 4.35.0, after a cold `lake build`.

| metric | direction | goal it serves | how to measure | now | floor (= now) | target |
|---|---|---|---|---|---|---|
| unaudited-theorems (count of `theorem`/`lemma` declarations not named in the axiom audit) | lower is better | 2 | `echo $(( $(DECL \| wc -l) - $(grep -o '``VbmJournal\.[A-Za-z_0-9.]*' VbmJournalProofs/Axioms.lean \| sort -u \| wc -l) ))` where DECL is `grep -rhE '^\s*(@\[[^]]*\] *)?(private \|protected )?(theorem\|lemma) ' VbmJournal VbmJournalProofs` | 172 (of 264 declarations), 2026-11-18 | 172 | |
| axiom-audited-theorems (count of names in `VbmJournalProofs/Axioms.lean`, each checked by the build to use only the three standard axioms) | higher is better | 2 | `grep -o '``VbmJournal\.[A-Za-z_0-9.]*' VbmJournalProofs/Axioms.lean \| sort -u \| wc -l` | 92, 2026-11-18 | 92 | |
| forbidden-construct-lines (lines with `sorry`, `admit`, `native_decide` or `unsafe` as a word, in Lean sources and tests) | lower is better | 2 | `grep -rnwE 'sorry\|admit\|native_decide\|unsafe' VbmJournal VbmJournalProofs tests --include='*.lean' \| wc -l` | 0, 2026-11-18 | 0 | |
| proof-recheck-rejected-modules (modules whose proofs Lean's own checker rejects in a fresh process) | lower is better | 1, 2 | `.land/tool/bin/land-lean recheck --selftest` (prints `recheck: ... ok` or `REJECTED` per module; about 3.5 minutes) | 0, 2026-11-18 | 0 | |
| build-warnings (warnings in a cold build; `warningAsError` is on, so any is a failure) | lower is better | 6 | `rm -rf .lake/build && lake build 2>&1 \| grep -ci warning` (removes the build cache; prints the count) | 0, 2026-11-18 | 0 | |
| trusted-c-code-lines (non-blank, non-comment lines of the one trusted C file) | lower is better | 3 | `grep -cvE '^\s*(//\|/\*\|\*\|$)' native/vbm_journal.c` | 148, 2026-11-18 | 148 | |
| trust-ledger-gaps (ledger entries with no written contract or no test, as `land-lean trust` counts them) | lower is better | 3 | `.land/tool/bin/land-lean trust` (read the number before `with no written contract or no test`) | 6 (of 11 entries, 18 required items covered), 2026-11-18 | 6 | |
| trust-ledger-uncovered-items (items the tree requires and the ledger does not cover; the gate fails above 0) | lower is better | 3 | `.land/tool/bin/land-lean trust; echo $?` (exit 0 = none) | 0, 2026-11-18 | 0 | |
| verified-core-lines (lines of the Lean implementation and model, `Init` only, the code that is compiled and linked) | lower is better | 3 | `cat VbmJournal/*.lean \| wc -l` | 1574, 2026-11-18 | 1574 | |
| differential-test-milliseconds (the driver over the real shims against the model, the SHA-256 and jsonl suites) | lower is better | 4, 6 | `s=$(date +%s%N); .lake/build/bin/vbm-journal-test >/dev/null; echo $(( ($(date +%s%N)-s)/1000000 ))` | 711, 2026-11-18 | 711 | |
| crash-test-milliseconds (`kill -9` of a signed writer in a loop, then recovery) | lower is better | 4, 6 | `s=$(date +%s%N); tests/crash.sh >/dev/null; echo $(( ($(date +%s%N)-s)/1000000 ))` | 1310, 2026-11-18 | 1310 | |
| proof-recheck-seconds (the slowest stage of Tier 1) | lower is better | 6 | `s=$(date +%s); .land/tool/bin/land-lean recheck --selftest >/dev/null; echo $(( $(date +%s)-s ))` | 213, 2026-11-18 | 213 | |
| tier1-seconds (all of `mise exec -- tests/tier1.sh`; land.conf's template comment says a target under 60 s) | lower is better | 6 | `s=$(date +%s); mise exec -- tests/tier1.sh >/dev/null; echo $(( $(date +%s)-s ))` | unmeasured: the harness runs Tier 1, not this worker; the stages measured here sum to about 227 s (cold build 12 + tests 1 + crash 1 + trust 0 + recheck 213) | | |
| read-signed-50mb-milliseconds (verify chain and signature of a 50 MB, 199,646-record JSON-lines journal) | lower is better | 5 | `lake build vbm-journal-bench && .lake/build/bin/vbm-journal-bench /tmp/j.journal 50 jsonl; rm -f /tmp/j.journal` (read the `readSigned` line) | 2011, 2026-11-18 ((`docs/slice3.md` reports 5.0 s on its machine)) | 2011 | |
| read-signed-50mb-peak-kilobytes (`VmHWM` after `readSigned`, the same run) | lower is better | 5 | same command (the last `VmHWM:` line) | 193460, 2026-11-18 | 193460 | |
| release-tags (local tags `v*`; `VERSION` says 0.1.0; a consumer pins a signed tag) | higher is better | 5 | `git tag --list 'v*' \| wc -l` | 0, 2026-11-18 (local clone only; origin unreachable from the jail, so remote tags unchecked) | 0 | |
| vendored-tool-drift-exit-code (0 = `.land/tool` is exactly its pin, v0.21.0) | lower is better | 6 | `.land/tool/bin/land-check; echo $?` | 0, 2026-11-18 | 0 | |
| power-cut-durability-tests (tests that cut power, or fault-inject a block device, to check the `fsync` and `rename` assumptions T2, T3, T6, T8) | higher is better | 3 | no command: no such test exists; `docs/trust-ledger.md:24` says "revisit with a fault-injecting block device" | unmeasured: needs a fault-injecting block device or a VM | | |

History (date, metric: value): 2026-11-18, all rows above: first measurement (this draft).

## Health today

- **Nothing is regressed**: no floor is below a stated goal, because no target is set yet and every floor is the first measurement.
- **Unmeasured**: `tier1-seconds` (only its stages are known, about 227 s) and `power-cut-durability-tests` (no test can exist short of a block-device fault injector). Remote `release-tags` is unchecked.
- **Far from where the goals point**: the proof recheck alone takes 213 s, against a Tier 1 whose template target is 60 s, and "everything runs before the push, once" makes that time the cost of every landing. Of 264 theorems, 172 are not in the axiom audit (many are helper lemmas, which the recheck replays but the axiom list does not name). Six of eleven trust-ledger entries lack a written contract or a test (the ledger itself says so: the contract is the model, the assumptions A1, A4, A9, A10 have no written source in this repository). There is no release tag, so the library cannot yet be pinned by a host although goal 5 is "consumable by a host".
- **Healthy**: zero forbidden constructs, zero warnings, zero rejected modules, the pin intact, one trusted C file of 148 lines, the 50 MB read in 2 s and 193 MB, within what `docs/slice3.md` reports.

## What a steward would do first

1. Cut the first signed release tag (`.agents/skills/release-a-library`), moving `release-tags` from 0 to 1, so that a host can pin the library (goal 5).
2. Write the missing contracts and tests of the trust ledger (the trust boundary text that `docs/slice1.md:32` cites as `docs/trust-boundary.md` is not in this repository), moving `trust-ledger-gaps` from 6 toward 0.
3. Find where the 213 s of the proof recheck go (two modules replayed side by side, the second replays the first's closure) and bring `proof-recheck-seconds`, and so `tier1-seconds`, down; measure `tier1-seconds` itself in the same step.

## Questions for the owner

- Targets: every `target` cell is blank. In particular, what is the budget of Tier 1 (`tier1-seconds`, `proof-recheck-seconds`)? The 60 s is a template comment in `.land/land.conf`, not a decision.
- Which of the 172 unaudited theorems must be audited: all, or only the headline theorems of each family? (`unaudited-theorems` would then count only those.)
- Is a smaller verified core (`verified-core-lines`) a goal, or only a smaller trusted C? The repository says nothing on the first.
- Is a release tag a goal now (the README says "made consumable by a host", `VERSION` is 0.1.0, no tag exists), and which host consumes it (lung?)? Is there a speed goal for the read of a journal (`docs/slice3.md:58` says not a gate), and at what size?
- Should the differences from lung (`docs/slice1.md:38`-`docs/slice1.md:42`, `docs/slice2.md:55`-`docs/slice2.md:69`) be a metric, as a count of open differences, and is lung's own journal meant to be replaced by this library?
- Are the assumptions A1, A4, A9, A10 to be written down in this repository (`docs/trust-boundary.md` is cited but absent), and is a power-cut test in scope?
