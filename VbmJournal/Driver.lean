import VbmJournal.World
import VbmJournal.Sig
/-! # vbm-journal slice 2, part 3: the interpreter and the driver

`Shims m` is the table of what the operating system does (docs/trust-ledger.md): the effects of the model, `write`, `fsync`, `fsyncDir`, `readAll` and
`truncate`, on the journal file, and `putSig` and `getSig`, on its signature file. The digest (`sha256`) is the eighth shim, a pure function
(`VbmJournal.Sha256`). The driver is generic in the monad `m`: `VbmJournal.Real` instantiates it with the real shims (in `IO`), `VbmJournal.Sim` with
their Lean models (a state monad over the file), and **the same code** runs in both. `VbmJournalProofs.Impl` proves that over the models it is the model of slice 1.

The driver is `Machine.step` and a loop: take the plan the machine made for an event, perform its effects in order through the table, feed the bytes
a `readAll` returned back to the machine as `readReply`, and acknowledge the plan. A shim that fails (an `m`-exception) is fatal to the writer: the
machine sees `crash` and the writer is idle (what slice 1 says of an effect that fails). -/
namespace VbmJournal

/-- The table of shims, in the monad `m`. Each operates on the journal named when the table is made. -/
structure Shims (m : Type → Type) where
  /-- Append these bytes to the journal file, creating it if there is none. -/
  write : Bytes → m Unit
  /-- Make everything written to the journal file durable. -/
  fsync : m Unit
  /-- Make the journal file's directory entry durable. -/
  fsyncDir : m Unit
  /-- The whole journal file (empty when there is none). -/
  readAll : m ByteArray
  /-- Cut the journal file back to this length, durably. -/
  truncate : Nat → m Unit
  /-- Replace the signature file with these bytes, atomically (all of them or none), durably. -/
  putSig : Bytes → m Unit
  /-- The signature file (`none` when there is none). -/
  getSig : m (Option Bytes)

section
variable {m : Type → Type} [Monad m] [MonadExcept String m]

/-- Perform one effect; a `readAll` returns the bytes. -/
def Shims.perform (sh : Shims m) : Effect → m (Option ByteArray)
  | .write b => do sh.write b; pure none
  | .fsync => do sh.fsync; pure none
  | .fsyncDir => do sh.fsyncDir; pure none
  | .readAll => do pure (some (← sh.readAll))
  | .truncate n => do sh.truncate n; pure none

/-- Perform a plan in order; the bytes of its `readAll`, if it has one. -/
def Shims.runPlan (sh : Shims m) : List Effect → m (Option ByteArray)
  | [] => pure none
  | e :: es => do
    let r ← sh.perform e
    let r' ← sh.runPlan es
    pure (match r' with | none => r | some b => some b)

/-- Acknowledge the plan of a state that is waiting for one (every effect completed). -/
def ack (P : Params) (st : St) : St :=
  if st.mode.isBusy then (step P st (.acked st.gen)).1 else st

/-- One event of the writer, driven: the machine's plan performed, its read fed back, its plan acknowledged. `gate` sees the bytes of a read before
the machine does, and may refuse (throw). An exception of a shim or of the gate escapes. -/
def driveRaw (P : Params) (sh : Shims m) (gate : ByteArray → m Unit) (st : St) (ev : Event) : m St := do
  let (st1, plan) := step P st ev
  match ← sh.runPlan plan with
  | none => pure (ack P st1)
  | some bytes =>
    gate bytes
    let (st2, plan2) := stepReplyB P st1 st1.gen bytes
    let _ ← sh.runPlan plan2
    pure (ack P st2)

/-- An exception is fatal to the writer: it is idle again (`crash`), and the message is returned. -/
def guarded (P : Params) (st : St) (body : m St) : m (St × Option String) :=
  tryCatch (do let st' ← body; pure (st', none)) fun e => pure ((step P st .crash).1, some e)

/-- **The driver (unsigned)**: one event of a writer. Returns the writer's new state, and the message of a failure. -/
def drive (P : Params) (sh : Shims m) (st : St) (ev : Event) : m (St × Option String) :=
  guarded P st (driveRaw P sh (fun _ => pure ()) st ev)

/-! ## The signature -/

/-- Sign the head of a ready writer after its `c` records (nothing for a journal of none, or a writer that is not ready). -/
def signHead (mac : Nat → Digest → Bytes) (sh : Shims m) (st : St) : m Unit :=
  match st.mode with
  | .ready h c => if c = 0 then pure () else sh.putSig (Sig.make mac c h).toBytes
  | _ => pure ()

/-- Recovery's check of the journal against its signature, on the bytes it read. A journal that fails verification is the machine's to refuse; a
journal whose signature fails is refused here, before the machine writes anything. -/
def sigGate (P : Params) (mac : Nat → Digest → Bytes) (sh : Shims m) (bytes : ByteArray) : m Unit :=
  match readB P bytes with
  | none => pure ()
  | some r => do
    match verdict P mac r.entries (← sh.getSig) with
    | .error e => throw e
    | .ok _ => pure ()

/-- **The driver (signed)**: one event of a writer, with the head signed after every change and checked at recovery. -/
def driveSigned (P : Params) (mac : Nat → Digest → Bytes) (sh : Shims m) (st : St) (ev : Event) : m (St × Option String) :=
  guarded P st do
    let st' ← driveRaw P sh (sigGate P mac sh) st ev
    if st' ≠ st then signHead mac sh st'
    pure st'

/-- **The reader**: a journal's entries, its head and its signature's verdict, with no writer (fails closed). -/
def readSigned (P : Params) (mac : Nat → Digest → Bytes) (sh : Shims m) : m (Read × Verdict) := do
  match readB P (← sh.readAll) with
  | none => throw "journal: fails verification (edited, reordered, or a record missing)"
  | some r =>
    match verdict P mac r.entries (← sh.getSig) with
    | .error e => throw e
    | .ok v => pure (r, v)

end
end VbmJournal
