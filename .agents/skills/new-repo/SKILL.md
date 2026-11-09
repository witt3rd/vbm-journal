---
name: new-repo
description: >-
  Bootstrap a new repository that lands directly on main with vbm-land: create it, vendor vbm-land pinned, add the AGENTS.md block and land.conf, make the first landing. Use when starting a repository that only your own agents or you work in.
---

# new-repo: a repository that lands with vbm-land

Use only if the repository is yours alone (no outside contributors), main is not deployed, and Tier 1 can run in under a minute. Otherwise use pull requests.

## Steps

1. Create the repository and a first commit on `main` (`OWNER/NAME` is yours):
   ```
   gh repo create OWNER/NAME --private --clone && cd NAME
   printf '# NAME\n' > README.md && git add -A && git commit -m 'chore: initial commit' && git push -u origin main
   ```
2. Vendor vbm-land, pinned to a release tag (`TAG`, for example the newest `v*` tag). It writes `.land/tool/`, `.land/PIN`, the `.land/land-direct` stub, `.agents/skills/` and a starter `.land/land.conf`; it commits nothing:
   ```
   gh api repos/OWNER/vbm-land/contents/install?ref=TAG -H 'Accept: application/vnd.github.raw' | bash -s -- --source OWNER/vbm-land TAG
   ```
3. Edit `.land/land.conf`: set `LAND_TEST_CMD` and/or `LAND_GATES_CMD` to this repository's Tier 1 (under 60 s); add `LAND_PROTECTED=.land/land.conf .land/land.d/* .land/land-direct` (or `.land/*`, one entry).
4. Paste `.land/tool/templates/AGENTS-block.md` at the top of `AGENTS.md` (create it if absent).
5. Protect the branch, on GitHub (the lander never force-pushes; make the remote refuse it too). The ruleset refuses deletion and non-fast-forward updates of the default branch, has no required pull request and no bypass list, so direct fast-forward landing still works:
   ```
   gh api repos/OWNER/NAME/rulesets --input .land/tool/templates/ruleset-protect-main.json
   gh api repos/OWNER/NAME/rulesets --input .land/tool/templates/ruleset-protect-release-tags.json
   gh api repos/OWNER/NAME/rules/branches/main --jq '.[].type'     # deletion, non_fast_forward
   ```
   Before the repository goes public, do every item of `.land/tool/templates/PUBLIC-REPO-SETTINGS.md` (fork pull-request workflows need approval for all outside contributors, a read-only workflow token that cannot approve pull requests, private vulnerability reporting, secret scanning with push protection, delete head branches on merge), including the runners item: if the private phase used a self-hosted runner (`runs-on: self-hosted`, with `.github/visibility` = `private`), before going public put `runs-on` back to hosted, remove the runner, leave `LAND_RED_MODE` unchanged, and set `.github/visibility` to `public` (the lint fails otherwise).
6. Verify the drift check and the land-time checks, then commit as one change:
   ```
   .land/tool/bin/land-check
   git checkout -b setup && git add -A && git commit -m 'chore(land): vbm-land vX.Y.Z'
   .land/land-direct --check
   ```
7. First landing: `.land/land-direct` (it is also the proof that landing works under the ruleset). With no `.land/land.conf` on main yet, the lander uses your working copy of it (first landing only).

## Verify

- `.land/land-direct` exits 0 and its last stdout line has `"result":"landed"`.
- `gh api repos/OWNER/NAME/rules/branches/main --jq '.[].type'` lists `deletion` and `non_fast_forward`.
- `.land/tool/bin/land-check` says `is intact`.

## Do NOT

- Do not push main yourself, or open a pull request.
- Do not edit anything under `.land/tool/`, `.land/land-direct` or `.agents/skills/<vbm-land skill>`: the drift check fails. Change vbm-land upstream.
- Do not use this for a repository with outside contributors or a deployed main.
