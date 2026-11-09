---
name: triage-red
description: >-
  Main is red (its Tier 1 fails on main's own tip): revert the commit that made it red, then reproduce and resubmit. Use when Tier 1 fails on a fresh checkout of main, or when your commit was reverted.
---

# triage-red

Nothing runs after the push, so a red main is found by whoever runs Tier 1 on it next (a lander's run, a worker, you). Red does **not** stop landing (a landing must not ADD a failure; one main already has is "inherited red").

## If you find main red

1. Confirm it on a fresh worktree of `origin/main` with the Tier 1 command from `.land/land.conf`.
2. Find the commit that made it red: `git bisect start origin/main <last known good>` then `git bisect run <Tier 1 command>`.
3. Revert it, as a true revert, in a new worktree: `git revert <sha>` and land it with `.land/land-direct`. Tell its author.

## If your commit was reverted

Reproduce in a **new worktree** off fresh `origin/main`; fix; resubmit through `.land/land-direct`. Never hotfix on main.

## Do NOT

- Do not push to main directly, or edit on main ("hotfix").
- Do not remove a hold or freeze you did not set (see `hold-and-freeze`).
- Do not re-run Tier 1 repeatedly to make a real red go away.
