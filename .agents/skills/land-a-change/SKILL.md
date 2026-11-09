---
name: land-a-change
description: >-
  The one way to land a change on main in a repository that uses vbm-land: scripts/land-direct. Covers reading the exit code and the JSON summary, local versus CI numbers, and what red means. Use whenever you have a finished local commit to put on main.
---

# land-a-change

There is exactly one way: `scripts/land-direct` (a stub for the vendored `scripts/land/bin/land-direct`), run from your worktree. It rebases onto fresh `origin/main`, runs Tier 1 on that exact combination, and pushes a plain fast-forward.

## Steps

1. Work in a worktree off fresh `origin/main`; commit with Conventional Commits (`type(scope): summary`). Keep the diff within the size budget (default 150 production lines; over it, split, or add a `Diff-Budget: <decomposition note>` trailer only with a real plan).
2. Cheap pre-check (commit messages, size budget, no push): `scripts/land-direct --check`. Full rehearsal without the push: `scripts/land-direct --dry-run`.
3. Land: `scripts/land-direct`. Bound it: `timeout 1900 scripts/land-direct`.
4. Read the **last line of stdout**, JSON: `{"sha","commits","tier1_seconds","result","exit"}`. Use `jq`: `... | tail -n1 | jq -r .result`.
5. Act on the exit code:

| exit | result | do |
|---|---|---|
| 0 | landed | start the next change from a fresh `origin/main`; nothing runs after the push |
| 1 | error | the message says why (base kept moving, bad commit subject, over budget): fix, run again |
| 11 | conflict | files are named: `git fetch && git rebase origin/main`, resolve, run again |
| 12 | refused | a hook, the protected-set rule or the drift check refused; read the message; never edit `scripts/land/` |
| 13 | tier1 | your change fails Tier 1; nothing landed; fix and run again |
| 14 | held | a hold or freeze is on; see `hold-and-freeze`; do not remove it unless you set it |
| 16 | moved | main moved faster than the lander could validate; nothing landed; just run it again (a rerun after an accepted push says "already landed" and exits 0) |


## A gate line that must go: the approval, announced first

A removed or changed line in a gate-defining file that may only gain lines (exit 12, "may only GAIN lines") lands only through a gate-edit approval (`scripts/land/docs/gate-edit-approvals.md`; `scripts/land/bin/land-direct --print-gate-diff-hash FILE` prints the hash). The order is fixed: (1) the approval record lands ALONE: one line, no other file, its own commit and landing; (2) **announce the approval commit to the independent judge BEFORE the edit commit, always, with the diff hash and the FULL edit diff** (`land-direct` prints `APPROVAL COMMIT: announce to the judge before landing the edit`); (3) the edit lands later and removes the record in the same landing. An agent with landing rights could write its own approval line: the control is that the judge reads the record before the edit lands. Never put the approval and the edit in one commit or one landing (refused), never reuse or quietly delete an approval.

## A protected path (when the repository sets `LAND_PROTECTED_LIST`)

A landing that touches a path of the protected-paths list is refused (exit 12, "touches the protected set") unless a one-time approval for exactly that set of paths and exactly that diff is on main. A resume or go-ahead message is not an approval: only the line on main is. The same order as above: `land-direct --print-gate-diff-hash @protected` prints the record (set, hash); the record lands ALONE, announced to the judge first; the change lands later and removes the record in the same landing. Never write the line for a change you are about to land yourself without the judge having read it.

## What red means

Nothing runs after the push: Tier 1 on the rebased combination is the only gate. If main is ever red, whoever sees it reverts the commit that made it red with `git revert` and lands the revert; its author reproduces in a new worktree and resubmits (`triage-red`). Your landing must not ADD a failure.

## Do NOT

- Never `git push origin main`, never force-push, never open a PR, never push a branch to land.
- Never retry exit 13 or 12 in a loop hoping it passes; read the failing step.
- Never hotfix on main: revert, reproduce in a new worktree, resubmit.
