# Pinned packages: vendoring a second signed source like vbm-land itself

A repository that vendors vbm-land (`scripts/land/`) can vendor **another signed package** the same way: `scripts/NAME/` is a pinned copy, `scripts/NAME/PIN` and `scripts/NAME/MANIFEST.sha256` say exactly which,
the drift check fails on any difference, and the repository **overrides nothing**. The first package is the gate set (`vbm-gates`, `scripts/gates/`). One flow handles N packages; this tool knows nothing about what a package contains.

## What a package source is

A git repository with `VERSION` (plain `X.Y.Z`), `MANIFEST.sha256` (`<sha256>  <path>` per file, sorted by path: the same format as this repository's), and **signed, annotated release tags** `vX.Y.Z` whose message carries
`manifest_sha256=<sha256 of MANIFEST.sha256>` (what `bin/land-release` makes). Everything the manifest lists is installed to `scripts/NAME/<path>`, nothing else. Paths are plain and relative (no `..`, no `PIN`, no `MANIFEST.sha256`).
Nothing of a package runs while it is installed or updated; the files are hashed against the manifest, and the manifest against the signed tag, before anything is written.

**Mode follows content:** a file is executable iff it starts with `#!`. The signed manifest therefore covers the executable bit, and the offline check can verify it without the source.

## Trust: one signers file per package

`scripts/NAME.signers` (an ssh allowed-signers file, the consumer's own, reviewed like a key change) lists who may sign NAME's releases. It is **not** `scripts/land.signers`: trusting vbm-land's key says nothing about
another source, and a package's key rotates on its own. The same key may be listed in both files; the consumer decides. The first install takes the file with `--signers FILE` (public key, checked out of band, see `signing.md`);
a package with no signers file is **refused**, never "UNVERIFIED" (vbm-land's own first install may be unverified; a package's may not).

## Install, update, check

```
scripts/land/bin/land-update --pkg gates --source OWNER/vbm-gates --signers FILE vX.Y.Z   # first install (stages scripts/gates/, scripts/gates.signers; commits nothing)
scripts/land/bin/land-update --pkg gates --diff vX.Y.Z      # verify, then show changed / added / removed files and the CHANGELOG entries since the pin
scripts/land/bin/land-update --pkg gates --land vX.Y.Z      # verify, stage, commit `chore(land): gates vX.Y.Z`, land through the repository's own lander and Tier 1, from a pristine clone
scripts/land/bin/land-update --pkg gates --check            # pinned vs the source's releases: 0 current, 1 behind, 2 not installed, 3 source unreachable
scripts/land/bin/land-update --pkg gates --auto             # the scheduled mode; the policy is the repository's LAND_AUTO_UPDATE (one policy for what may update itself), a major is never automatic
```
After the first install, the PIN's `source` is the only source (`--source` is refused). The PIN is the same documented `key=value` file as vbm-land's. `--land` trailers are `<Trailer>: vbm-land-update-NAME-<version>`.

## The drift check

`scripts/land/bin/land-check` (no arguments) checks **vbm-land and every pinned package** it finds (`scripts/*/PIN`): the manifest hashes to the pin, every listed file matches its hash and its mode, nothing else is in the directory,
and `scripts/NAME.conf` has only known keys. A `scripts/*/` directory with a `MANIFEST.sha256` but no `PIN` is drift (deleting the pin must not switch the check off). `--pkg NAME` checks one; `--upstream` also confirms the manifest at the
pinned commit with the source. The lander runs it on the rebased tree, so a landing that edits a vendored package is refused (exit 12) like one that edits `scripts/land/`. Restore, never edit:
`scripts/land/bin/land-update --pkg NAME <pinned version>`.

## Variation: `scripts/NAME.conf`, known keys only

The repository's only lever. Data, not code: `NAME_KEY=value` lines (NAME upper-cased, `-` as `_`), `#` comments, one pair of quotes around a value, nothing expanded or run. The package ships `scripts/NAME/KEYS` (one key per line,
`#` comments) naming the keys it understands; **an unknown key fails the drift check**, and so does a line that is not `NAME_KEY=value`. A package reads its configuration with `. scripts/land/lib/pkg.sh; pkgconf_load NAME scripts/NAME.conf scripts/NAME/KEYS`
(the same function the check runs, so reader and check cannot disagree); value validation is the package's own. There is no override directory and no per-file patch hook. A missing feature is a new release of the package.
