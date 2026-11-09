---
name: hold-and-freeze
description: >-
  Stop landings with a hold marker or a freeze, and lift them. Use when a person or an incident requires landing to stop (hold), or only fixes and reverts to land (freeze), and when land-direct exits 14.
---

# hold-and-freeze

Markers live in `<git common dir>/vbm-land/`, shared by every worktree of the clone.

| | hold | freeze |
|---|---|---|
| effect | **no** landing at all (even one in flight, checked right before its push) | only a fix or revert lands |
| use | a person needs to stop everything now; maintenance; unsure state | main broke and a revert/fix is being prepared |
| needs | a reason | reason, **owner**, expiry |

## Steps

```
.land/land-direct --status                                       # shows the hold (and freeze) state
.land/land-direct --hold "why, who, until when"                  # stop landings
.land/land-direct --release                                      # allow landings again
.land/land-direct --freeze "why" --owner NAME --for 6h           # only fixes and reverts land
.land/land-direct --thaw                                         # lift it (it also lifts on expiry or a landed fix)
```

When `land-direct` exits 14, read the marker's reason (`--status`), and ask its owner. A red main is not a reason to freeze: whoever sees it reverts what made it red with `git revert` (`triage-red`).

## Verify

`.land/land-direct --status` shows `hold: none` after `--release`; a landing attempt while held exits 14 and pushes nothing.

## Do NOT

- Do not remove a hold or freeze you did not set; the reason names the owner.
- Do not delete marker files by hand; use `--release` / `--thaw`.
- Do not hold to avoid a red Tier 1 or a conflict; fix those.
- Do not set a freeze without an owner and an expiry (both are required).
