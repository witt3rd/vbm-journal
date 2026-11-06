---
name: update-vbm-land
description: >-
  Update the pinned, vendored copy of vbm-land in a repository (land-update), read the "behind" report of the scheduled check, verify a signed release, and understand the manifest. Use when land-check reports drift, when the weekly vbm-land-update workflow says the repository is behind, or when asked to bump vbm-land.
---

# update-vbm-land

A repository vendors a pinned copy: `scripts/land/` (tool, templates), `scripts/land/PIN` (source, version, 40-hex commit, manifest hash, signature status), the `scripts/land-direct` entry script (yours after the first install), the vbm-land skills in `.agents/skills/`, and the scheduled workflow `.github/workflows/vbm-land-update.yml` (yours). `MANIFEST.sha256` lists the hash of every vendored file; all of them are drift-checked. Updates are **pulled by the repository**: vbm-land knows nothing about what vendors it (docs/update-propagation.md in the source).

## Know where you stand

```
scripts/land/bin/land-check              # offline: the copy still equals its pin (0 ok, 1 drift, 2 not installed)
scripts/land/bin/land-check --upstream   # also asks the source about the pinned commit (3: source unreachable)
scripts/land/bin/land-update --check     # read-only: "pinned vX, latest vY: behind N releases (patch|minor|major)" (0 current, 1 behind, 3 unreachable)
```
The weekly workflow runs the drift check and `land-update --auto`; "behind" shows as a warning and a summary line. It is a reminder, never a gate.

## Update (the repository's own act)

1. `scripts/land/bin/land-update --diff vX.Y.Z`: verifies the release (below) and shows the changed, added and removed vendored files, their diffs and the CHANGELOG entries since your pin. Read it: new keys, exit codes, "Upgrade notes". A **major** release needs a person's decision.
2. `scripts/land/bin/land-update --land vX.Y.Z` from a clean worktree: verify, stage, commit `chore(land): vbm-land vX.Y.Z` (with the trailers your `land.conf` requires) and land it through **your own** lander and gates, run from a pristine clone of the base branch. A hold, a red main, a failed Tier 1, a refusing hook or the attack suite stops it with the lander's exit code; the commit stays local; nothing is forced.
   Or by hand: `scripts/land/bin/land-update vX.Y.Z` (stages only), `scripts/land/bin/land-check`, review `git status`, one commit, `scripts/land-direct`.
3. After the landing read the push CI of the base branch.

**The weekly schedule** is shipped only when the source is public (`.github/visibility` = `public` in the source at install time); while it is private the workflow is dispatch-only and the check is `scripts/land/bin/land-update --check` by hand (or Run workflow). When the source flips to public, add the `schedule:` trigger back to your workflow (checklist item 11 in `scripts/land/templates/PUBLIC-REPO-SETTINGS.md`).

**Automatic updates** are the repository's choice: `LAND_AUTO_UPDATE=patch|minor` in `scripts/land.conf` (default `none`) lets the weekly workflow do step 2 itself with a push token the repository holds (`VBM_LAND_PUSH_TOKEN`), on a runner with your Tier 1 toolchain. A major release is never automatic. If it fails, the workflow fails visibly: read it and do step 1 and 2 by hand.

## Other pinned packages (`scripts/NAME/`, for example the gate set)

The same commands with `--pkg NAME`: `scripts/land/bin/land-update --pkg NAME --check | --diff vX | --land vX`; a first install is `--pkg NAME --source SRC --signers FILE vX` (the maintainer's public key, out of band, lands as `scripts/NAME.signers`: a package without one is refused). `scripts/land/bin/land-check` checks vbm-land and every pinned package; `DRIFT:` is fixed by restoring (`land-update --pkg NAME <pinned version>`), never by editing the copy or its PIN or MANIFEST. The only variation is `scripts/NAME.conf` (known keys only: an unknown key fails the check). docs/packages.md in the source (`scripts/land/docs/packages.md`).

## Signed releases

A release is an annotated tag signed by the maintainer's ssh key, recording the hash of `MANIFEST.sha256`. List the public keys you trust in `scripts/land.signers` (an ssh allowed-signers file from the source, taken out of band: `install --signers FILE` on the first install). With that file, `land-update` and `install` **refuse** anything that is not such a tag (a commit, a lightweight or unsigned tag, an unknown signer, a manifest hash that differs) **before** anything of the release runs or is written. Without it they say `UNVERIFIED` and the PIN records `signature=unverified`: add the file. A change to `scripts/land.signers` is a key change: it is reviewed like one.

## Drift

`DRIFT:` lines name the file. Fix by **restoring**, not editing: `scripts/land/bin/land-update <pinned version>` (the version is in `scripts/land/PIN`). A local need becomes a config key or a hook in your own `scripts/land.d/`, or a change upstream.

## Editing a gate line in a consumer (the approval)

A removed or changed line in a gate-defining file (`LAND_GATE_APPEND_ONLY`, or what your own judge guards) lands only through a gate-edit approval already on main: a record `FILE | sha256 of the exact diff | reason | date` in `scripts/gate-edit-approvals.txt`, hash from `scripts/land/bin/land-direct --print-gate-diff-hash FILE`. **The approval commit lands alone (one line, no other file) and is announced to the independent judge BEFORE the edit commit, always, with the diff hash and the FULL edit diff**; the edit's landing then removes the record (one-time, 7 days). Honest limit: an agent with landing rights could write its own approval line; the control is that approvals are visible one-commit records the judge reads before the edit lands. A vbm-land update that adds a gate to an existing repository does not need an approval; changing an existing gate line does.

## Do NOT

- Do not edit `scripts/land/`, `MANIFEST.sha256`, `PIN` or the vendored skills by hand, and never "fix" drift by regenerating the manifest in a consumer.
- Do not update to an untagged commit unless asked, and do not skip verification (never remove `scripts/land.signers` to make an update pass).
- Do not mix the update with other changes in one commit.
- Do not take a major release without the owner's decision.
- Do not land a gate-line edit and its approval together, and do not land the edit before the approval commit has been announced to the judge.
