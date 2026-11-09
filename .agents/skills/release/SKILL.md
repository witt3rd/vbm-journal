---
name: release
description: >-
  Cut a vbm-land release: regenerate and verify MANIFEST.sha256, bump VERSION, update CHANGELOG, land, then tag the landed commit. Use only when working in the vbm-land source repository and a new version is due.
---

# release (vbm-land source repository)

A release is a tag whose commit has a fresh `MANIFEST.sha256` (it hashes every vendored file, including `skills/*/SKILL.md`). Consumers pin the commit, so a tag is only trustworthy on a commit that already landed on main through the lander (its Tier 1 green).

Versioning: additive interface changes (config keys, exit codes, JSON keys, hook or marker names, new skills) are minor; anything else is major. `CHANGELOG.md` gets a line per interface change.

## Steps

1. Fresh worktree off `origin/main`. Set `VERSION` (no `v`, e.g. `0.4.0`); add the `CHANGELOG.md` entry.
2. `bin/land-manifest && bin/land-manifest --check` (the lander regenerates it too).
3. `timeout 600 tests/run.sh` (Tier 1).
4. Commit `chore(release): vX.Y.Z` and land: `bin/land-direct` (this repository lands itself; `.land/land-direct` is its wrapper).
5. Tag the landed commit and push the tag:
   ```
   git fetch origin && git tag vX.Y.Z <landed-sha> && git push origin vX.Y.Z
   ```
6. Verify from a scratch repository:
   `git init -q /tmp/t && /path/to/vbm-land/install --source OWNER/vbm-land --target /tmp/t vX.Y.Z && /tmp/t/.land/tool/bin/land-check`

## Do NOT

- Never move or delete a pushed tag; cut a new version.
- Never tag a commit that did not land through the lander.
- Never tag with a stale manifest (`bin/land-manifest --check` must pass).
- Do not announce a release before step 6 passes.
