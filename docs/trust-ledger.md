# The trust ledger

Everything outside our direct control that vbm-journal executes or depends on: the code we did not prove, and the facilities we assume. The trusted C is **one file, `native/vbm_journal.c` (170 lines, 148 of code)**, and nothing else is trusted code: the driver, the signature, HMAC and the chain are Lean, proved (`docs/slice2.md`). Each shim below is the real counterpart of a Lean model (`VbmJournal/Sim.lean`, `VbmJournal/Sha256.lean`); the proofs run the driver over the models, the tests check that the C does what its model does.

Entry format: **What** it is; **Enters** where it enters; **Assumes** what we assume of it (the contract); **Test** the test that can fail; **Owner**; **Plan** (verify, replace, sandbox or accept, with a reason); **Covers** the keys it accounts for (`land-lean trust` derives what must be covered from the tree: vbm-land `docs/lean-gates.md`). The entries were numbered S1 to S7 and P1 to P3; they are T1 to T10 in that order.

## The shims (native/vbm_journal.c)

Each shim takes the path of the file it acts on (the journal's, or its signature's, `<journal>.sig`), opens it, acts, closes it: no descriptor is kept between effects. A failing shim returns an error (an exception in `m`); the driver treats it as a crash of the writer (`VbmJournal.guarded`).

### T1. `write` (`vbm_write`; model `Fs.run … (.write b)`)
- **What:** `open(O_WRONLY|O_APPEND|O_CREAT, 0600)`, a loop of `write(2)` until every byte is written (retrying `EINTR`), `close`.
- **Enters:** `Shims.real` (`VbmJournal/Real.lean`), the effect `Effect.write`.
- **Assumes:** the bytes reach the file at its end and in order (`O_APPEND`); on a failure or a crash any prefix of them may be in the file (the model's `Fs.crash`: a crash keeps the durable bytes and any prefix of the pending ones). Not assumed: durability (that is `fsync`). The contract is the model: `VbmJournal/Sim.lean`.
- **Test:** `tests/Main.lean`, `Rig`: after every effect the real file's bytes are compared with the model file's (`Fs.run`), on the golden cases, the tampered files and 400 random scripts; the real crash test (`tests/crash.sh`, `kill -9` of a writer in a loop).
- **Plan:** verify the model against POSIX only by test; accept.
- **Owner:** the owner
- **Covers:** `extern:vbm_write`

### T2. `fsync` (`vbm_fsync`; model `.fsync`)
- **What:** `open(O_RDONLY)`, `fsync(2)`, `close`.
- **Assumes:** when it returns, every byte written to the file (by an earlier `write` shim, which has closed its descriptor) is durable: a crash afterwards keeps it (assumption A4 of the trust boundary of the harness this library was extracted from: no written contract in this repository). A write-back error that no descriptor has reported yet is reported to the descriptor opened here (Linux `errseq`); a failure is fatal to the writer, never retried.
- **Test:** as S1 (the effect sequence is what the model says); the crash test. The durability itself cannot be tested without cutting the power: it is the assumption (`tests/Main.lean`; the crash test is `tests/crash.sh`).
- **Plan:** accept because it is one POSIX call whose contract is the assumption above, tested against its model; revisit with a fault-injecting block device.
- **Enters:** `Shims.real` (`VbmJournal/Real.lean`: `realFsync`)
- **Owner:** the owner
- **Covers:** `extern:vbm_fsync`

### T3. `fsyncDir` (`vbm_fsync_dir`; model `.fsyncDir`)
- **What:** `open` of the file's directory (`O_RDONLY|O_DIRECTORY`), `fsync`, `close`. The directory is the path up to the last `/` (`.` when there is none).
- **Assumes:** when it returns, the file's directory entry is durable: a crash afterwards does not lose the file (A10). Lung syncs the directory only when it creates the file; the model syncs it on the first record and after every recovery (`docs/slice1.md`).
- **Test:** as S1 (it must succeed on the test directory); not testable otherwise (`tests/Main.lean`; the crash test is `tests/crash.sh`).
- **Plan:** accept because it is one POSIX call whose contract is the assumption above, tested against its model.
- **Enters:** `Shims.real` (`VbmJournal/Real.lean`: `realFsyncDir`)
- **Owner:** the owner
- **Covers:** `extern:vbm_fsync_dir`

### T4. `truncate` (`vbm_truncate`; model `.truncate n`)
- **What:** `open(O_WRONLY)` (no create), `ftruncate`, `fsync`, `close`.
- **Assumes:** afterwards the file is its first `n` bytes and that is durable (lung's `journalTruncate`). The contract is the model: `VbmJournal/Sim.lean`.
- **Test:** the torn-tail golden case and the random scripts (recovery truncates to the verified length) (`tests/Main.lean`; the crash test is `tests/crash.sh`).
- **Plan:** accept because it is one POSIX call whose contract is the assumption above, tested against its model.
- **Enters:** `Shims.real` (`VbmJournal/Real.lean`: `realTruncate`)
- **Owner:** the owner
- **Covers:** `extern:vbm_truncate`

### T5. `readFile` (`vbm_read_file`; model `readAll`, `getSig`)
- **What:** `open(O_RDONLY)`, a loop of `read(2)`, `close`; `none` when the file does not exist (`ENOENT`), an error for any other failure.
- **Assumes:** it returns every byte of the file, including bytes written and not yet synced (the page cache), as a reader after a crash would find the durable ones. The contract is the model: `VbmJournal/Sim.lean`.
- **Test:** as S1 (every effect compares the real file with the model's); the reader after every event of every script (`tests/Main.lean`; the crash test is `tests/crash.sh`).
- **Plan:** accept because it is one POSIX operation whose contract is the assumption above, tested against its model.
- **Enters:** `Shims.real` (`VbmJournal/Real.lean`: `realReadFile`)
- **Owner:** the owner
- **Covers:** `extern:vbm_read_file`

### T6. `replace` (`vbm_replace`; model `putSig`)
- **What:** write `<path>.tmp` (`O_CREAT|O_TRUNC`, mode 0600), `fsync` it, `rename(2)` it over `<path>`, `fsync` the directory. Used only for the signature file.
- **Assumes:** `rename` is atomic: after a crash the file is the old signature or the new, whole; and when `replace` returns, it is the new, durable. (A torn signature would be refused, fail-closed, `verdict_unreadable`; the atomic rename is what keeps a crash from making the journal unreadable.) The contract is the model: `VbmJournal/Sim.lean`.
- **Test:** as S1: the signature file after every `putSig` is compared with the bytes put; the reader after every event (`tests/Main.lean`; the crash test is `tests/crash.sh`).
- **Plan:** accept because it is one POSIX operation whose contract is the assumption above, tested against its model.
- **Enters:** `Shims.real` (`VbmJournal/Real.lean`: `realReplace`)
- **Owner:** the owner
- **Covers:** `extern:vbm_replace`

### T7. `sha256` (`vbm_sha256`; model `sha256Model`, FIPS 180-4 in Lean)
- **What:** a self-contained SHA-256 (one shot), about 50 lines of C.
- **Assumes:** it is SHA-256. For the proofs a second assumption, about the function and not the C: it is collision resistant (`Sha256.CollisionFree`, assumption A9 of the trust boundary of the harness this library was extracted from, no written contract in this repository), the hypothesis of `real_lawful`.
- **Test:** `tests/Main.lean` `shaTests`: FIPS 180-4 and RFC 4231 known answers (the empty message, `abc`, two blocks, a million `a`), and the C against the Lean model on 200 random inputs of every length from 0 to 199 (the block boundaries). The Lean model is the algorithm written out, and itself passes the known answers.
- **Plan:** verify the Lean model (and drop the C) when a verified SHA-256 in Lean is fast enough to be the shim; until then accept.
- **Enters:** `VbmJournal/Sha256.lean` (the `sha256` shim, `@[extern "vbm_sha256"]`)
- **Owner:** the owner
- **Covers:** `extern:vbm_sha256`

### Not trusted: HMAC-SHA256, the chain, the signature
HMAC (RFC 2104) is **not** a shim: `hmacSha256` is Lean over the `sha256` shim (`VbmJournal/Sha256.lean`), tested against RFC 4231 (including a key longer than a block). The hex encoding, the digest chain, the signature file, the verdict and the driver are Lean and proved.

## The platform

### T8. The operating system and the file system
- **What:** POSIX `open`, `write`, `read`, `fsync`, `ftruncate`, `rename`, and the file system under them.
- **Assumes:** the contract of the shims above, and the model of docs/slice1.md: writes reach the file in order; a crash keeps the durable bytes and any prefix of the unsynced ones; `fsync` makes data durable; a file whose directory entry was not made durable may be gone (A1, A4, A10). A write or an `fsync` that fails leaves the file as a crash at that point could have left it (the model of an error: `Sim`, `simEff`).
- **Test:** none that can fail short of a power cut; the real crash test kills the writer, not the machine.
- **Plan:** accept because the operating system is outside what a library can prove; the shims' assumptions above state exactly what is relied on.
- **Enters:** every shim runs on it: `native/vbm_journal.c`.
- **Owner:** the owner
- **Covers:** `file:native/vbm_journal.c`

### T9. The Lean toolchain (pinned: 4.35.0) and the C compiler
- **What:** the Lean compiler and kernel, the runtime (`lean.h`, `libleanrt`, which the C uses to build and read `ByteArray`s and results), and `cc` (the system C compiler, `-std=c11 -Wall -Wextra -Werror`) that compiles `native/vbm_journal.c`.
- **Assumes:** the kernel is sound and the compiler is faithful (a miscompile of the driver or the C would void the proofs); `lean.h` is used as documented. (no written contract beyond the compiler's own documentation)
- **Test:** the differential test runs the compiled driver against the model; `lake build` checks the proofs and that they use the standard axioms only (`VbmJournalProofs/Axioms.lean`).
- **Plan:** accept because the compiler and kernel are outside this repository and every proof assumes them.
- **Enters:** the whole build: `lean-toolchain`, `mise.toml`, `lakefile.lean`, and the C of `native/vbm_journal.c`.
- **Owner:** the owner
- **Covers:** `file:lean-toolchain` `file:mise.toml` `file:lakefile.lean` `lean-compiler` `lean-runtime` `clang-lld`

### T10. The test program (`tests/Main.lean`, `tests/crash.sh`)
- **What:** Lean and shell, not part of the library and never linked into it. It is trusted only to fail when the shims differ from their models.
- **Assumes:** that it checks what it says (it was checked by breaking a shim: a `write` that appends a stray byte fails the differential test). (no written contract: it is its own check)
- **Plan:** accept because it is trusted only to fail when a shim differs from its model, and was checked by breaking a shim.
- **Enters:** `tests/Main.lean`, `tests/crash.sh` (run by the Tier 1 script, never linked into the library).
- **Test:** none: it is itself the test, checked by breaking a shim (a `write` that appends a stray byte fails it).
- **Owner:** the owner
- **Covers:** `file:tests/Main.lean` `file:tests/crash.sh`

### T11. The build and ledger tools: lake and python3
- **What:** `lake` builds the library, its proofs and the test program; `python3` runs the trust-ledger checker of the landing tool.
- **Enters:** `lakefile.lean`, `tests/tier1.sh`.
- **Assumes:** both behave as documented (a wrong build would be caught by the proofs and the differential test, a wrong checker by its own negative self-tests): no written contract.
- **Test:** none beyond the tools' own; the proofs and the differential test fail on a wrong build.
- **Owner:** the owner
- **Plan:** accept because they are the host's own tools and nothing here executes in an artifact through them.
- **Covers:** `tool:lake` `tool:python3`
