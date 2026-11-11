---
name: release-a-library
description: >-
  Cut a signed release tag on any repository with land-release, so that others can pin it with land-pin vendor. Use when a library has a version to publish or a consumer needs something to pin.
---

# release-a-library

A release is a signed, annotated tag `vX.Y.Z` on `origin/main`'s head. Its message records `tree_sha256=` (the tree hash of the exported tree), which is what `land-pin vendor` checks. The tool is `.land/tool/bin/land-release` (the contract is `docs/pin.md`).

Versioning: before 1.0, a change a consumer can see (exported names, the ABI, a specification clause) is a minor version; a change that alters none of it is a patch. The first release is `0.1.0`.

## Steps
1. Put the version in `VERSION` as plain `X.Y.Z` and land it through the lander. The commit to release must be `origin/main`'s head.
2. On the host that holds the release key (the key never leaves it): `LAND_SIGNING_KEY=<path to the key> .land/tool/bin/land-release --push`. It refuses a dirty tree, a head that is not `origin/main`, a stale manifest where the repository has one, and an existing tag.
3. Verify from a scratch clone: `git -c gpg.format=ssh -c gpg.ssh.allowedSignersFile=.land/land.signers verify-tag vX.Y.Z`, and run `land-pin vendor` for the new tag in a scratch repository.
4. Bump the consumers' pins, each in its own change (skill `vendor-a-library`).

## Do not
- Move or delete a pushed tag (the repository rules forbid it): cut a new version.
- Tag by hand: only `land-release` records the tree hash.
- Copy the release key off its host or put it in a repository.
