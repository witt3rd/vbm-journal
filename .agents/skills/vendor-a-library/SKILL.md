---
name: vendor-a-library
description: >-
  Add, bump or check a library this repository vendors (vendor/NAME and .land/pins.lock) with land-pin. Use when a repository depends on another vbm library, when a bump is due, or when its fast gate reports a pin failure.
---

# vendor-a-library

One way, one tool: `.land/tool/bin/land-pin` (the contract is `docs/pin.md` in vbm-land). A library is vendored as source at `vendor/NAME/` and listed in `.land/pins.lock`; it is never fetched at build time.

## Steps
1. Add or bump: `.land/tool/bin/land-pin vendor NAME URL vX.Y.Z`. It REFUSES unless the tag is annotated, signed by a key in `.land/land.signers`, records exactly one `tree_sha256=`, and the exported tree matches it; a refusal changes nothing. Commit `vendor/NAME/` and the lock together: a bump is one commit.
2. Require it by path in the build file (Lean: `require «vbm-x» from "vendor/vbm-x"`) and name its files as `__dir__ / "vendor" / "vbm-x" / ...`. Never `from git`, never a `.lake/packages` path, never code that looks for a sibling.
3. Put `.land/tool/bin/land-pin verify` in the repository's fast gate. Put `.land/tool/bin/land-pin online` in the scheduled slow tier: it refuses a moved, deleted or unreachable tag and reports newer ones without applying them.

## Verify
`land-pin verify` exits 0. Editing, adding or deleting any file under `vendor/NAME/` (outside `.lake/`) makes it exit 1.

## Do not
- Patch a vendored file: change the library upstream, release it, bump the pin.
- Edit `.land/pins.lock` by hand, or loosen it: it is a protected path of the repository.
- Leave two versions of one library in the closure: when two vendored libraries carry different copies of a third, `verify` refuses; bump the older one upstream.
