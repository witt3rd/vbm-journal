import VbmJournal.Basic
/-! # vbm-journal slice 1, part 2: the writer as a pure function, and the effect interface as data

`step P st ev` is a pure function from a state and an event to a new state and a **plan**: the list of effects the interpreter must
perform. The effects are the whole interface to the world: `write`, `fsync`, `fsyncDir`, `readAll`, and `truncate` (lung's
`journalTruncate`, which drops a torn tail before appending again; the brief's four effects cannot do that, see `Effect.truncate`).
Nothing here runs an effect; `VbmJournal.World` gives them their meaning. -/
namespace VbmJournal

/-- The effect interface. A plan is performed in order; a crash may stop it anywhere. -/
inductive Effect where
  /-- Append these bytes at the end of the file (one `write`; a crash may keep any prefix of them). -/
  | write (bytes : Bytes)
  /-- Make everything written so far durable. -/
  | fsync
  /-- Make the file's directory entry durable (after the file was created). -/
  | fsyncDir
  /-- Read the whole file; its bytes come back as the next event (`Event.readReply`). -/
  | readAll
  /-- Cut the file back to `len` bytes, durably (lung's `journalTruncate`: `ftruncate` then `fsync`). Not in the brief's list of four;
  lung's recovery needs it to drop a torn tail, so slice 2's shim table needs it too. -/
  | truncate (len : Nat)
  deriving DecidableEq, Repr

/-- Where the live writer is. The writer is always the one of the current generation (`St.gen`). -/
inductive Mode where
  /-- No live writer: the process died, or nobody has opened the journal. -/
  | idle
  /-- A writer took the place and has not yet recovered. -/
  | opened
  /-- A writer is reading the file, to recover. -/
  | reading
  /-- A recovered writer, idle between appends: the head and the number of records it has made durable. -/
  | ready (head : Digest) (count : Nat)
  /-- A plan is outstanding; when it is acknowledged the writer is `ready` at this head and count. -/
  | busy (head : Digest) (count : Nat)
  /-- Recovery found a journal that fails verification and refuses to write (fails closed). -/
  | broken
  deriving DecidableEq, Repr

/-- The writer state: the generation of the latest take-over (the fence) and the live writer's mode. -/
structure St where
  gen : Nat
  mode : Mode
  deriving DecidableEq, Repr

/-- The state before any writer: generation 0, nobody live. -/
def St.init : St := ⟨0, .idle⟩

/-- What happens to the writer. Every event of a writer carries the generation the writer holds. -/
inductive Event where
  /-- A new writer takes the place with the next generation; any older writer is fenced. -/
  | takeOver
  /-- The process died (or an effect failed: an append error is fatal to the writer). -/
  | crash
  /-- The writer of this generation starts recovery. -/
  | recover (g : Nat)
  /-- The bytes `readAll` returned. -/
  | readReply (g : Nat) (bytes : Bytes)
  /-- The writer of this generation appends an entry. -/
  | append (g : Nat) (e : Entry)
  /-- Every effect of the outstanding plan has completed. -/
  | acked (g : Nat)
  deriving DecidableEq, Repr

/-- The plan that makes a change durable: cut the file to `cut` bytes (if asked), write `data` and `fsync` (if there is any), then
make the directory entry durable (if asked). -/
def commitPlan (cut : Option Nat) (data : Bytes) (dir : Bool) : List Effect :=
  (match cut with | some n => [Effect.truncate n] | none => []) ++
  (if data = [] then [] else [Effect.write data, Effect.fsync]) ++
  (if dir then [Effect.fsyncDir] else [])

/-- Recovery, once the bytes are read: verify (fail closed), cut a torn tail, settle every call in flight as interrupted, and make the
file and its directory entry durable. The truncate is to the verified length (a no-op when there is no torn tail). -/
def recoverPlan (P : Params) (st : St) (bytes : Bytes) : St × List Effect :=
  match read P bytes with
  | none => (⟨st.gen, .broken⟩, [])
  | some r =>
    let ss := settleEntries r.entries
    if bytes = [] then (⟨st.gen, .busy r.head 0⟩, [])
    else (⟨st.gen, .busy (headFrom P r.head ss) (r.entries.length + ss.length)⟩,
          commitPlan (some (bytes.length - r.tail.length)) (encodeFrom P r.head ss) true)

/-- **The model**: a pure function from a state and an event to the new state and the plan. A writer event of a stale generation, or
at the wrong time, changes nothing and plans nothing (it is refused). -/
def step (P : Params) (st : St) : Event → St × List Effect
  | .takeOver => (⟨st.gen + 1, .opened⟩, [])
  | .crash => (⟨st.gen, .idle⟩, [])
  | .recover g =>
    if g = st.gen then
      match st.mode with
      | .opened => (⟨st.gen, .reading⟩, [.readAll])
      | _ => (st, [])
    else (st, [])
  | .readReply g bytes =>
    if g = st.gen then
      match st.mode with
      | .reading => recoverPlan P st bytes
      | _ => (st, [])
    else (st, [])
  | .append g e =>
    if g = st.gen then
      match st.mode with
      | .ready h c => (⟨st.gen, .busy (P.link h (P.enc e)) (c + 1)⟩, commitPlan none (encodeFrom P h [e]) (c == 0))
      | _ => (st, [])
    else (st, [])
  | .acked g =>
    if g = st.gen then
      match st.mode with
      | .busy h c => (⟨st.gen, .ready h c⟩, [])
      | _ => (st, [])
    else (st, [])

/-! ## The reply of a read, on a flat buffer

The driver reads the file as a `ByteArray` and hands it to the machine as it is: `stepReplyB` is `step` on `Event.readReply g b.toList`
(`VbmJournalProofs.Flat`, `stepReplyB_eq`), without the list. -/

/-- `recoverPlan` on a flat buffer. -/
def recoverPlanB (P : Params) (st : St) (bytes : ByteArray) : St × List Effect :=
  match readB P bytes with
  | none => (⟨st.gen, .broken⟩, [])
  | some r =>
    let ss := settleEntries r.entries
    if bytes.size = 0 then (⟨st.gen, .busy r.head 0⟩, [])
    else (⟨st.gen, .busy (headFrom P r.head ss) (r.entries.length + ss.length)⟩,
          commitPlan (some (bytes.size - r.tail.length)) (encodeFrom P r.head ss) true)

/-- The machine's step on the reply of a read, the bytes flat. -/
def stepReplyB (P : Params) (st : St) (g : Nat) (bytes : ByteArray) : St × List Effect :=
  if g = st.gen then
    match st.mode with
    | .reading => recoverPlanB P st bytes
    | _ => (st, [])
  else (st, [])

end VbmJournal
