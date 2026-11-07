import VbmJournal.Machine
/-! # vbm-journal slice 1, part 3: the world the effects act on

The meaning of the effect interface, as a pure model of one file: what a `write` and an `fsync` do, and what a crash leaves.
`World` is the writer state together with the file; `World.step` is one event of the whole system, with the crash point of an
operation as a parameter, so that every crash of every operation is one of the model's events.

Assumed of the operating system (docs/trust-boundary.md A1, A4, A10): a `write` reaches the file in order, a crash keeps durable
bytes and any prefix of the bytes written since the last `fsync`, an `fsync` makes everything written durable, and a file whose
directory entry was not made durable may be gone after a crash. A plan runs to its end, or to a crash, before the next event
(one interpreter per journal; the fence is the generation check). -/
namespace VbmJournal

/-- One file. `pending` is what was written and not yet synced. -/
structure Fs where
  durable : Bytes
  pending : Bytes
  dirSafe : Bool
  deriving DecidableEq, Repr

/-- No file. -/
def Fs.empty : Fs := ⟨[], [], false⟩

/-- What `readAll` returns. -/
def Fs.contents (f : Fs) : Bytes := f.durable ++ f.pending

/-- The meaning of one effect. `readAll` changes nothing (its reply is `contents`). -/
def Fs.run (f : Fs) : Effect → Fs
  | .write bs => { f with pending := f.pending ++ bs }
  | .fsync => { f with durable := f.durable ++ f.pending, pending := [] }
  | .fsyncDir => { f with dirSafe := true }
  | .readAll => f
  | .truncate n => { f with durable := (f.durable ++ f.pending).take n, pending := [] }

/-- A crash. The file keeps its durable bytes and the first `keep` bytes of what was pending; if its directory entry was not durable
it may be gone (`vanish`). -/
def Fs.crash (f : Fs) (keep : Nat) (vanish : Bool) : Fs :=
  if vanish && !f.dirSafe then Fs.empty
  else { f with durable := f.durable ++ f.pending.take keep, pending := [] }

/-- Perform the first `n` effects of a plan. -/
def Fs.runPrefix (f : Fs) (n : Nat) (plan : List Effect) : Fs := (plan.take n).foldl Fs.run f

/-- Perform a whole plan. -/
def Fs.runAll (f : Fs) (plan : List Effect) : Fs := plan.foldl Fs.run f

/-- Where an operation's plan stops: a crash after `n` effects, keeping `keep` bytes of the unsynced write, and the file vanishing
or not when its directory entry is not durable. -/
structure Cut where
  n : Nat
  keep : Nat
  vanish : Bool
  deriving DecidableEq, Repr

/-- The writer and the file. -/
structure World where
  m : St
  fs : Fs
  deriving DecidableEq, Repr

/-- The start: no writer, no file. -/
def World.init : World := ⟨St.init, Fs.empty⟩

/-- An event of the whole system. A writer event names the generation of the writer; `cut` is where it crashes (`none`: it does not). -/
inductive WEvent where
  | takeOver
  | crash (keep : Nat) (vanish : Bool)
  | recover (g : Nat) (cut : Option Cut)
  | append (g : Nat) (e : Entry) (cut : Option Cut)
  deriving DecidableEq, Repr

/-- Is a plan outstanding? -/
def Mode.isBusy : Mode → Bool
  | .busy _ _ => true
  | _ => false

/-- Perform the plan the machine asked for, then acknowledge it; or, with a `cut`, perform the first `n` effects, crash, and let the machine see the crash. -/
def World.finish (P : Params) (w : World) (m1 : St) (plan : List Effect) : Option Cut → World
  | none => ⟨(VbmJournal.step P m1 (.acked m1.gen)).1, w.fs.runAll plan⟩
  | some c => ⟨(VbmJournal.step P m1 .crash).1, (w.fs.runPrefix c.n plan).crash c.keep c.vanish⟩

/-- One event of the system: the pure model, then the effects it planned acting on the file. A refused event (the machine did not change state) changes nothing. -/
def World.step (P : Params) (w : World) : WEvent → World
  | .takeOver => ⟨(VbmJournal.step P w.m .takeOver).1, w.fs⟩
  | .crash keep vanish => ⟨(VbmJournal.step P w.m .crash).1, w.fs.crash keep vanish⟩
  | .append g e cut =>
    match VbmJournal.step P w.m (.append g e) with
    | (m1, plan) => if m1 = w.m then w else w.finish P m1 plan cut
  | .recover g cut =>
    match VbmJournal.step P w.m (.recover g) with
    | (m1, _) =>
      if m1 = w.m then w
      else
        match VbmJournal.step P m1 (.readReply g w.fs.contents) with
        | (m2, plan) => if m2.mode.isBusy then w.finish P m2 plan cut else ⟨m2, w.fs⟩

/-- Run a list of events. -/
def World.run (P : Params) (w : World) (evs : List WEvent) : World := evs.foldl (World.step P) w

/-- A new process takes over and recovers (no crash). -/
def World.reopen (P : Params) (w : World) : World :=
  let w1 := w.step P .takeOver
  w1.step P (.recover w1.m.gen none)

/-- A new process takes over and recovers, and crashes at `cut` in the middle of the recovery. -/
def World.reopenCut (P : Params) (w : World) (cut : Cut) : World :=
  let w1 := w.step P .takeOver
  w1.step P (.recover w1.m.gen (some cut))

end VbmJournal
