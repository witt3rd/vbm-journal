import VbmJournal.Driver
/-! # vbm-journal slice 2, part 5: the shims' models

The Lean model of the table of shims: the operating system as a state (the journal file `Fs`, the signature file, and where a crash comes) in a
state monad that can fail. This is what the proofs run the driver over (`VbmJournalProofs.Impl`); the real shims (`VbmJournal.Real`) are assumed to
do what these do (docs/trust-ledger.md, each entry's **Assumes**), and the differential test (`tests/Main.lean`) checks that they do.

The files of the model are those of slice 1: a `write` and `fsync` act on `Fs` as `Fs.run` says. A **fault** is a crash at an effect: `cut` names the
effect (the `n`-th effect that changes the journal file, counting from `done`) and what the crash leaves (`keep`, `vanish`, as in `Fs.crash`); the
effect fails, the file is what a crash at that point leaves, and the driver sees an exception. A real shim that fails is assumed to leave a file a
crash at that point could have left. -/
namespace VbmJournal

/-- The model of the operating system. `done` counts the effects performed on the journal file. -/
structure Sim where
  fs : Fs
  sig : Option Bytes
  cut : Option Cut
  done : Nat

/-- The monad of the model: a state, and failure (the state kept when it fails). Written out, so that what it does is plain. -/
abbrev SimM (α : Type) : Type := Sim → Except String α × Sim

instance : Monad SimM where
  pure a := fun s => (Except.ok a, s)
  bind x f := fun s =>
    match x s with
    | (Except.ok a, s') => f a s'
    | (Except.error e, s') => (Except.error e, s')

instance : MonadExcept String SimM where
  throw e := fun s => (Except.error e, s)
  tryCatch x h := fun s =>
    match x s with
    | (Except.ok a, s') => (Except.ok a, s')
    | (Except.error e, s') => h e s'

/-- An effect that changes the journal file; at the cut, it fails and the file is what the crash leaves. -/
def simEff (f : Fs → Fs) : SimM Unit := fun s =>
  match s.cut with
  | some c =>
    if s.done = c.n then (Except.error "cut", { s with fs := s.fs.crash c.keep c.vanish })
    else (Except.ok (), { s with fs := f s.fs, done := s.done + 1 })
  | none => (Except.ok (), { s with fs := f s.fs, done := s.done + 1 })

/-- **The model of the table**: each shim as the slice 1 model of its effect. -/
def Shims.sim : Shims SimM where
  write b := simEff (·.run (.write b))
  fsync := simEff (·.run .fsync)
  fsyncDir := simEff (·.run .fsyncDir)
  readAll := fun s => (Except.ok s.fs.contents, s)
  truncate n := simEff (·.run (.truncate n))
  putSig b := fun s => (Except.ok (), { s with sig := some b })
  getSig := fun s => (Except.ok s.sig, s)

/-- Run an action of the model from a state. -/
def SimM.go {α : Type} (x : SimM α) (s : Sim) : Except String α × Sim := x s

end VbmJournal
