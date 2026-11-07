# Slice 2: the verified implementation over a table of shims

The model of slice 1 (`docs/slice1.md`) as a program: an interpreter that performs the model's effects through a small table of trusted shims, the driver that takes over, recovers, appends and reads, and the signed head file (`<journal>.sig`), with a proof that the program run over the shims' **models** is the slice 1 model, step for step. Everything in `VbmJournal/` is Lean (`Init` only) except `native/vbm_journal.c`, the only trusted code (`docs/trust-ledger.md`).

## The pieces

| Module | What |
|---|---|
| `Sha256` | `sha256` (an `@[extern]` shim whose Lean body, `sha256Model`, is FIPS 180-4 written out), `hexOf`, `hmacSha256` (RFC 2104 **in Lean over the shim**: not a shim) |
| `Sig` | the signature file (`Sig.toBytes`/`ofBytes`: `index head mac`, decimal and spaces), `macInput` = `"index:head"`, `verdict` (lung's `LungSpec.JournalSig.verdict`: fails closed on an unreadable file, a wrong mac, a journal cut back below the signed index, a chain that is not the signed head; the records after the signed index are an unsigned tail) |
| `Driver` | `Shims m` (the table), `Shims.perform`/`runPlan` (the interpreter), `driveRaw`, `drive` (one event of the writer: plan, read, reply, acknowledge; an exception is a crash), `driveSigned` (signs the head after every change, checks the signature at recovery before writing anything), `readSigned` (the reader). Generic in the monad `m`: the same code runs over the real shims and over their models |
| `Real` | the six IO shims as `@[extern]` declarations, `Shims.real path`, `Params.real` (the SHA-256 chain: `link p b = hex(sha256(chainInput p b))`, the unary codec) |
| `Sim` | the models of the shims: the file (`Fs`), the signature file, and a fault (`Cut`) in a state monad that can fail |

## The shim table

Seven shims, each in `native/vbm_journal.c` with a Lean model. `path` is the journal's, or `<journal>.sig`.

| Shim | C | Model | What |
|---|---|---|---|
| `write` | `vbm_write` | `Fs.run (.write b)` | append the bytes (create the file, mode 0600) |
| `fsync` | `vbm_fsync` | `Fs.run .fsync` | everything written is durable |
| `fsyncDir` | `vbm_fsync_dir` | `Fs.run .fsyncDir` | the file's directory entry is durable |
| `truncate` | `vbm_truncate` | `Fs.run (.truncate n)` | cut the file to `n` bytes, durably |
| `readFile` | `vbm_read_file` | `readAll`, `getSig` | the whole file, or none |
| `replace` | `vbm_replace` | `putSig` | the file becomes exactly these bytes, atomically (tmp, fsync, rename, fsync the directory) |
| `sha256` | `vbm_sha256` | `sha256Model` | the digest |

HMAC-SHA256 is derived in Lean (the brief's table lists it): six shims are IO, one is the hash, and the trusted C is 170 lines, 148 of code, about 50 of them SHA-256. `truncate` (slice 1's fifth effect) and `replace`/`readFile` (the signature file) are the additions to the brief's list.

## The theorems

Standard axioms only, no `sorry` (`VbmJournalProofs/Axioms.lean` fails the build otherwise). `Impl.step P w ev` is one event of the system with the driver as the writer, run over the models of the shims, with a fault at any effect (`Cut`) and the crash after a plan that finished first (`World.finish`).

| | Theorem | Module |
|---|---|---|
| **the implementation is the model** | `impl_step_eq`: `Impl.step P w ev = World.step P w ev`, for every event, every crash point and every `w` the machine is not waiting in; `impl_run_eq`, `impl_reachable`: any list of events | `Impl` |
| slice 1 transfers | `impl_append_only`, `impl_verifies`, `impl_crash_consistency`, `impl_reopen_idempotent`, `impl_reopen_settles`, `impl_stale_append`, `impl_stale_recover`, `impl_takeOver_fences`: the five families of slice 1, restated of the driver | `Transfer` |
| what a plan does | `runPlan_nocut`, `runPlan_cut` (a plan performs its effects on the file; a fault at an effect leaves what a crash there leaves), `drive_planned`, `drive_recover` | `Impl` |
| signature file | `sig_roundtrip` (what is signed is read back), `parseDec_natDec` | `Sig` |
| verification fails closed | `verdict_sound`, `verdict_signed`, `verdict_unreadable`, `verdict_bad_mac`, `verdict_cut_back`, `verdict_rewritten`, `verdict_unsigned_only`; `verdict_anchored`, `signed_unique` (an accepted signature anchors the journal: slice 1's `Anchored`: a journal cut back at its tail, which verifies by the chain alone, is refused) | `Sig` |
| the driver signs | `signed_append_ok`, `signed_append_verifies` (the signature of a completed append is accepted, no unsigned tail), `signed_append_fault` (a failed append leaves the signature as it was), `signed_recover_refused` (**recovery refuses a journal whose signature fails, writing nothing**), `signed_recover_ok`, `signed_recover_verifies` | `SigImpl` |
| honest through crashes | `signed_step`, `signed_reachable`: from the start, any events with any crash points: the journal is the model's (`World.run`) and the signature file is the signature of a prefix of it (or none); `signed_reachable_verifies`: the verifier accepts it | `SigWorld` |
| the real parameters | `real_lawful`: `Params.real` meets `Params.Lawful` **if** `sha256` is collision resistant (`Sha256.CollisionFree`) | `Real` |

## What is assumed, and what is not proved

- **The shims do what their models do** (`docs/trust-ledger.md`, one entry each): the real counterpart of `Sim`. Tested, not proved; durability and atomic rename are the operating system's.
- **A shim that fails is a crash.** The model of an error is a crash at that effect (the file is what a crash there leaves). A real failed `write`/`fsync` leaves a state a crash could have left; the writer is dead (`guarded`), the next process recovers.
- **SHA-256 is collision resistant** (hypothesis of `real_lawful`), and HMAC-SHA256 with a secret key is a MAC (the host's key is the root of trust: whoever has it can re-sign; a journal and its signature can be deleted together). Neither is a theorem.
- **A plan runs to its end, or to a crash, before the next event** (slice 1). One interpreter per journal at a time; the fence is the writer's generation. A zombie writer with a write already in flight after a take-over is not modelled, and the **cross-process lock** (lung's `flock` on `<journal>.lock`) is not in this library: it is the host's, until it becomes a shim.
- **The signature is written after the records it signs are durable, and the signature file itself is replaced atomically**, so a crash leaves an old signature (an unsigned tail, accepted) or the new one, never a torn one.
- The codec of `Params.real` is the unary one of slice 1 (`note n` is `n` bytes), enough for the driver and the tests; the codec is a parameter (`Params.enc`/`dec`) and lung's is slice 3's.

## Where it differs from lung

- The line is `digest ' ' body '\n'` (slice 1), lung's `{... "c": digest}` JSON; the chain input is `chainInput prev body` (a prefix code, so that the digest binds for every input), lung's `prev "\n" body`. The signature file is `index head mac`, lung's `{index, head, mac}` JSON; `mac` is lung's: hex of HMAC-SHA256 of `index:head`.
- Recovery syncs the directory whenever a file exists and always truncates to the verified length (`docs/slice1.md`).
- The signature is checked by recovery (`sigGate`) before anything is written, and by the reader (`readSigned`); the key is a parameter (`macReal key`), never read or created here (lung's `loadKey` stays the host's).

## What slice 3 (lung's switch) must change

1. **The line format and the chain input.** Lung's journals are JSON lines with the digest in the line, hashed as `sha256(prev "\n" body)`: they do not verify under `Params.real`. Either a one-time migration (read with the old code, write with the new) or make the line format a parameter of the model (`lineOf`, `splitLine`, `frame`: slice 1's `Basic` and the proofs that depend on it) and the chain input unambiguous for every `prev` (`link_binds` is universal).
2. **The entry and its codec.** `Entry` is `note`/`call`/`done`; lung's records are `SEvent`/`Action` with out-of-line text. Either map lung's records onto the three (`note` carries a handle) or make `Entry` a parameter, and give lung's JSON codec as `Params.enc`/`dec` with the codec laws (round trip, canonical, no newline).
3. **Bytes.** `Bytes` is `List UInt8` (the proofs' shape): reading a journal of megabytes allocates a list cell per byte. Before lung's journals (megabytes) run on it, `Bytes` should be `ByteArray` in the compiled code with a proof that the two agree (or a streaming read).
4. **The host keeps**: the writer's lock (`flock`), the key (`Lung.Sign.loadKey`, `LUNG_REQUIRE_SIG`), creating and resetting a fresh journal (`Journal.open`'s `reset`, `dropSig`), the `.beat` file. It replaces `Lung.journalAppend`, `journalTruncate`, `sha256Hex`, `hmacSha256Hex`, `Lung.Sign.sign`/`verify`, `LungSpec.JournalSig.verdict` and `LungSpec.JournalOpen` with `driveSigned`/`readSigned`, keeping the writer's `St` in an `IO.Ref`; `substrate/journal.c` shrinks to nothing (the HTTP substrate keeps OpenSSL for TLS).
5. **The slice 2 differences above** (directory sync, truncate) are the model's; lung's differential test on recorded journals (slice 1's "pool" item) compares them.

## Tests (Tier 1: `mise exec -- tests/tier1.sh`)

`lake build` (the proofs, the C, the test program), the `sorry` check, then `.lake/build/bin/vbm-journal-test`: SHA-256 and HMAC known answers, the C against the Lean model; **the differential test**: the driver over the real shims run on the slice 1 golden cases (`Examples.scripts`), the tampered files and 400 random scripts with crashes, against `World.step` (the machine state, the file's bytes and the model `Fs` compared after every event, and the real file against the model file after every effect; the reader must accept every journal that verifies); and `tests/crash.sh`, the real crash test: a writer appending signed records is killed (`SIGKILL`) three times and the journal is recovered and verified (the acknowledged records are there, in order, signed). A crash of the machine (power) is not tested: the model's `Fs.crash` is the assumption.
