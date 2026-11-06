---
name: triage-red
description: >-
  A push CI run of main failed (Tier 1 red), or you received a watchdog notice that your commit was reverted: find out what happened, reproduce in a new worktree and resubmit. Use when the watchdog reverted something, when land-revert alerted (exit 3), or when main's push CI is red.
---

# triage-red

Red = the `tier1` job of a push to main failed on CI. Red does **not** stop landing: the watchdog (`scripts/land/bin/land-revert`, run by `.github/workflows/vbm-land-revert.yml`) bisects the commits since the last green run with the repository's own Tier 1, reverts the first failing one as a true revert and lands it through the lander. The author is told by the `on-revert` hook (`LAND_REVERT_TASK`, `LAND_REVERT_AUTHOR`).

## If your commit was reverted

1. Read the revert commit on main (`git log --grep 'This reverts commit'`): it names your commit and carries your Task-ID.
2. Reproduce in a **new worktree** off fresh `origin/main` with the Tier 1 command from `scripts/land.conf`; fix; resubmit through `scripts/land-direct`. Never hotfix on main.

## If the watchdog alerted (exit 3) or did not run

It could not revert cleanly (a conflict with more than five later commits, the revert landing refused, a hold in force, no green run to bisect from). A person decides:

1. Find the run and the failing step: `gh run list --workflow ci.yml --branch main --limit 5`, `gh run view <id> --log-failed | tail -60`.
2. **Infrastructure** (runner never started, network, billing, cancelled): not red. Re-run it: `gh run rerun <id> --failed`.
3. **Real red**: run by hand `scripts/land/bin/land-revert --dry-run --bad <failing sha> --good <last green sha>` to see the culprit; then without `--dry-run`, or revert/fix forward yourself in a new worktree and land it (`fix(ci)` / `fix(tests)` / a git `Revert` commit).

## Do NOT

- Do not push to main directly, or edit on main ("hotfix").
- Do not remove a hold or freeze you did not set (see `hold-and-freeze`).
- Do not re-run CI repeatedly to make a real red go away.
