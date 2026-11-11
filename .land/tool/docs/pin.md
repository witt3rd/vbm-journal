# Pins and releases: one contract

Status: accepted 2026-11-11; the tools in this document are built from it, in the order of section 7. It replaces
the divergent per-repository pin scripts and the manual vendoring steps. It reuses what vbm-land already has: the
signers file `.land/land.signers`, tag signature verification (`lib/source.sh`), and `bin/land-release`.

## 1. The tree hash (one definition, used everywhere)

The tree hash of a directory is the SHA-256 of a text built like this:
- every regular file under the directory, EXCEPT anything inside a directory named `.lake` or `.git` AT ANY DEPTH
  (build products and version-control metadata; Lake builds a vendored library, and the libraries vendored inside it,
  in place);
- one line per file, `<sha256 of the file> <path relative to the directory>\n`;
- lines sorted bytewise (C locale), concatenated.
A symlink or a special file anywhere in the tree is an error. A path containing a newline or a backslash is an error
(`sha256sum` escapes both: never a silently different hash); every other path (a space, `#`, `<`, non-ASCII) is hashed
as it is, and the lines are sorted by bytes. The tree hash of a commit is the tree hash of its exported tree.

## 2. Releases

`bin/land-release` is the one release tool for every repository. It makes the annotated, SSH-signed tag
`v<VERSION>` on `origin/main`'s head, and the tag message records `tree_sha256=<tree hash of HEAD>` (vbm-land's own
tag also keeps `manifest_sha256=`, as today). Key custody is as in docs/signing.md: the key never leaves its host.
A tag is never moved or deleted.

## 3. The lock and the vendored copy

A repository vendors each direct dependency at `vendor/NAME/` and lists it in `.land/pins.lock`, one line each,
`#` comments allowed:

    NAME URL TAG REV TREE_SHA256

`TAG` is `vX.Y.Z`, `REV` 40 hex (the tag's commit), `TREE_SHA256` 64 hex. The lock is read strictly: a wrong field
count, a bad hex string, a duplicate name, a name that is not `[a-z0-9][a-z0-9_-]*` is an error (exit 2). The lock is
a protected path of the consumer: a change to it is the loosening an attacker would make.

## 4. Commands (`bin/land-pin`)

- `land-pin tree DIR`: print the tree hash of DIR.
- `land-pin vendor NAME URL TAG`: the ONLY way to add or move a pin. It fetches the tag, REFUSES unless the tag is
  signed by a key in `.land/land.signers` and its message has `tree_sha256=`, exports the tagged commit to
  `vendor/NAME/`, recomputes the tree hash and REFUSES unless it equals the recorded one, then writes the lock line.
  A bump is this command and one commit.
- `land-pin verify`: offline, fast; run by every repository's fast gate. Exit 0 only when ALL of:
  1. every lock line has `vendor/NAME/` and its tree hash equals the lock's;
  2. every directory directly under `vendor/` has a lock line (an unlocked vendored library is refused);
  3. every copy of a library found anywhere in the vendored tree, at any depth (a nested `vendor/*/vendor/NAME`),
     has the same tree hash as every other copy of it, and as the lock when the lock names it (ONE version of each
     package in the closure).
  Exit 1 with every reason when anything is wrong; exit 2 on a malformed lock.
- `land-pin online`: the slow tier. For every lock line, `git ls-remote URL refs/tags/TAG^{}` must equal REV (a moved
  or deleted tag is a finding); newer tags are reported, never applied.
- `land-pin list`: the names, one per line (for the trust ledger).

There is no fetch-on-missing mode: a missing vendored copy is a failure, never a download.

## 5. What each command must refuse (these are the negative tests, `tests/test_pin.sh`)

Edited, added, deleted vendored file; a symlink; an unlocked `vendor/` directory; a lock line with no directory; a
flipped lock hash; a malformed lock (each field, a duplicate, an unsafe name); a nested copy that differs (the
diamond); `vendor` on an unsigned tag, a tag signed by an unknown key, a tag whose message lacks `tree_sha256=` or
disagrees with the exported tree. And one thing it must ACCEPT: build products under `.lake/` inside a vendored
directory (Lake builds a path dependency in place).

## 6. Consequences

- A repository that carries its own pin script and lock deletes them. The `spec_hash` with per-consumer path lists
  and the module-root field go away: a vendored library is trusted whole and never patched.
- A release cut before this contract by hand has no `tree_sha256=` in its message, so `vendor` refuses it. Tags are
  immutable: the library gets a new version from `land-release`; the old tag stays unused.
- A fast gate that did not run the pin check (a lock read only by a scorer) now runs `land-pin verify`.

## 7. Build order (each a small change, tests first, each landing green)

1. `lib/verify.sh` (then `lib/treehash.sh`, merged into it by the one-verifier change), `land-pin tree` and `land-pin verify`, with the negative tests for them.
2. `land-pin vendor`, with its negative tests (unsigned, unknown key, missing or disagreeing `tree_sha256=`).
3. `land-pin online` and `list`; `land-release` records `tree_sha256=` and no longer requires vbm-land's own manifest
   for another repository; the skills and the README updated; a release.
