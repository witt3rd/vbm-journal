# Slice 1: the verified journal model

A pure Lean model of lung's journal (`VbmJournal/`, `Init` only, no IO) and its proofs (`VbmJournalProofs/`, standard axioms only). Nothing here runs against the operating system: slice 2 implements the model over a shim table and proves it equal to it.

## The model

| Module | What |
|---|---|
| `Basic` | `Entry`, `Params` (the digest chain and the codec, left open), the line format `digest ' ' body '\n'`, `parseLines` (torn tail), `verifyFrom`/`read` (fail closed), `openCalls`/`settleEntries` |
| `Machine` | `step : Params → St → Event → St × List Effect`, the writer as a pure function; `Effect` is the whole interface to the world: `write`, `fsync`, `fsyncDir`, `readAll`, `truncate` |
| `World` | what the effects do to one file (`Fs`: durable and pending bytes, directory entry), what a crash leaves, and `World.step`, one event of the whole system with the crash point of an operation as a parameter (`Cut`) |
| `Concrete`, `Examples` | the unary codec and a toy FNV digest; the scripted cases behind `tests/golden/slice1.golden` |

The state is the writer's generation (the fence) and its mode (`idle`, `opened`, `reading`, `ready head count`, `busy`, `broken`). Events: `takeOver`, `crash`, `recover g`, `readReply g bytes`, `append g e`, `acked g`. A writer event of a generation that is not current changes nothing and plans nothing.

`truncate` is a fifth effect: the brief names four, but lung's recovery cuts a torn tail with `journalTruncate` before appending again, and without it a torn tail would run into the next record. Slice 2's shim table needs it (or a `write` that can shorten).

## The theorems (statements first in `VbmJournalProofs/Theorems.lean` and `Chain.lean`)

| | Theorem | Module |
|---|---|---|
| (a) append-only | `append_only`, `append_only_reachable`: after any events with any crash points, the journal of an earlier state is a prefix of a later one's | `World`, `Theorems` |
| (b) chain integrity | `read_encode` (appends verify), `head_binds`, `verify_only_prefix` and `perm_verifies_only_if_same` (reordered, duplicated or deleted records fail), `edit_fails`, `anchored_unique` and `anchored_short_fails` (a cut or an edit before an anchor fails it) | `Chain` |
| (c) crash consistency | `crash_consistency`: a crash at any point of an append leaves the journal as before or after, never between; `crash_before_effects`, `crash_after_plan`, `recovered_after_crash` | `Theorems` |
| (d) fencing | `stale_refused`, `takeOver_fences`, `world_takeOver_fences`, `accepted_is_live`, `live_unique`, `gen_mono` | `Theorems` |
| (e) recovery | `reopen_settles` (every call in flight settled once: `settle_once`, `settle_closes`), `reopen_idempotent`, `reopen_crash_safe` (a crash at any point of recovery, then recovery, equals an uncut recovery) | `Theorems`, `Settle` |

`Axioms.lean` makes the build fail if any of them uses an axiom beyond `propext`, `Classical.choice`, `Quot.sound`. `Witness.lean` proves the laws the theorems assume (`Params.Lawful`) are satisfiable. `Golden.lean` compares `Examples.golden` with `tests/golden/slice1.golden` (Lake does not track that file: after editing it, touch `Golden.lean`).

## What is assumed, and what is not modelled

- **The digest binds** (`Params.Lawful.link_binds`): collision resistance of SHA-256, a hypothesis of the chain theorems, not a theorem (docs/trust-boundary.md A9). The toy digest of the golden file does not bind and the theorems do not apply to it; they apply to `Params.sym`, which does.
- **The operating system** (A1, A4, A10): writes reach the file in order; a crash keeps the durable bytes and any prefix of the unsynced ones; `fsync` makes them durable; a file whose directory entry was not made durable may be gone.
- **A plan runs to its end or to a crash before the next event.** A zombie writer with a write already in flight after a take-over is not modelled; the fence is the generation check at the machine.
- **The signature** (`Lung.Sign`, the HMAC file) is slice 2. The model has the anchor (`Anchored`: the head after `n` records, which lung signs) and proves what an anchor gives, but the state does not hold one, so a journal cut back at its tail verifies (the chain alone cannot tell).
- **The journal is the file's entries once its directory entry is durable.** Before that the file may vanish in a crash, so nothing in it is yet part of the journal (`World.records`).

## Where the model differs from lung today

- Recovery ends with an `fsyncDir` whenever a file exists. Lung syncs the directory only when it creates the file (`journal.c`, `!existed`), so a crash between the create and its directory sync leaves a file whose later appends never sync it. The model's append syncs the directory on the first record (count 0) and its recovery on any file.
- Recovery always truncates to the verified length (a no-op without a torn tail); lung truncates only when there is one.
- Entries are `note`, `call`, `done`: lung's `Action`/`SEvent` records are abstracted to what recovery needs.
