---
name: adopt-in-existing-repo
description: >-
  Convert an existing pull-request-flow repository to direct landing with vbm-land in seven steps. Use when asked to move a repository you own alone off PRs and merge queues onto land-direct.
---

# adopt-in-existing-repo

Precondition (all three): only your agents or you write to it; main is not deployed; Tier 1 can be under about 60 s. If not, stop: keep pull requests.

## Steps

1. **Define Tier 1.** Find or write one command that builds, lints and runs the fast tests, and time it: `time <cmd>`. Over 60 s: split off the slow checks to Tier 2 first.
2. **CI shape.** Make `.github/workflows/ci.yml` trigger Tier 1 on `push` to main only (job named `tier1`) and Tier 2 on a schedule (`scripts/land/templates/ci.yml.example` after step 3 shows the shape). Remove the `pull_request` trigger and any merge-queue workflow.
3. **Vendor vbm-land pinned**, in a fresh worktree off `origin/main`:
   `gh api repos/OWNER/vbm-land/contents/install?ref=TAG -H 'Accept: application/vnd.github.raw' | bash -s -- --source OWNER/vbm-land TAG`
4. **Configure** `scripts/land.conf`: `LAND_TEST_CMD`/`LAND_GATES_CMD` from step 1, `LAND_PROTECTED` (gate-defining files), `LAND_FIX_PATHS` (tests and CI), `LAND_PROD_PATHS`, and `LAND_REQUIRE_TRAILERS` if you use them. Start with `LAND_RED_MODE=push` if CI already runs on push, else `off`.
5. **Agent instructions.** Replace PR instructions in `AGENTS.md` with `scripts/land/templates/AGENTS-block.md`. Delete any "open a PR" text elsewhere.
6. **Land the adoption itself** with the new lander: `scripts/land/bin/land-check && git add -A && git commit -m 'chore(land): adopt vbm-land vX.Y.Z' && scripts/land-direct`. Then read the push CI.
7. **Retire the PR flow**: close open PRs after landing their content (or archive the diff and a reason first), turn off required reviews/merge queue in the repository's branch settings if you own them, and drop auto-merge bots. Check the three metrics next week (landings per hour, p90 commit-to-main, red minutes).

## Verify

`scripts/land/bin/land-check` ok; `scripts/land-direct --dry-run` ends `would-land`; after step 6 the push CI `tier1` is green.

## Do NOT

- Do not adopt where outside contributors exist or main deploys.
- Do not delete branches or PRs before saving their diff and a one-line reason.
- Do not change branch protection you do not own; ask its owner.
