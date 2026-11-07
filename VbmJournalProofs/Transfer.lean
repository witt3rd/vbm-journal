import VbmJournalProofs.Impl
/-! # The theorems of slice 1 hold of the implementation

`impl_step_eq` and `impl_reachable` (`VbmJournalProofs.Impl`) say that the driver over the models of the shims is the slice 1 model. So every
theorem of slice 1, which is about `World.step`, is a theorem about the driver. Here are the five families restated of it, each by that equality and
the slice 1 theorem: they are the statements the lung switch (slice 3) relies on.

`Impl.step P w ev` is one event of the system with the driver as the writer; `Impl.runAll` a list of them; `Impl.reopen` a new process that takes
over and recovers. `records w` is the journal (`World.records`). -/
namespace VbmJournal

variable {P : Params} {w : World}

theorem Inv.notBusy (hI : Inv P w) : ¬ w.m.mode.isBusy := by
  have := hI.rest
  cases h : w.m.mode <;> simp_all [Mode.Rest, Mode.isBusy]

/-- A new process takes over and recovers, with the driver. -/
def Impl.reopen (P : Params) (w : World) : World :=
  let w1 := Impl.step P w .takeOver
  Impl.step P w1 (.recover w1.m.gen none)

theorem impl_reopen_eq (hI : Inv P w) : Impl.reopen P w = w.reopen P := by
  have hb := hI.notBusy
  simp only [Impl.reopen, World.reopen]
  rw [impl_step_eq w hb .takeOver, impl_step_eq _ (notBusy_step w hb .takeOver) _]

section Lawful
variable (L : P.Lawful)
include L

/-- **(a) Append-only, of the implementation.** After any events with any crash points, the journal only grows. -/
theorem impl_append_only (evs₁ evs₂ : List WEvent) :
    World.records P (Impl.runAll P World.init evs₁) <+: World.records P (Impl.runAll P World.init (evs₁ ++ evs₂)) := by
  rw [impl_reachable, impl_reachable]
  exact append_only_reachable L evs₁ evs₂

/-- **(b) The journal the implementation leaves verifies.** -/
theorem impl_verifies (evs : List WEvent) : ∃ r, read P (Impl.runAll P World.init evs).fs.contents = some r := by
  rw [impl_reachable]
  exact reachable_verifies L evs

/-- **(c) Crash consistency, of the implementation.** A crash at any point of an append leaves the journal as it was or as it is once the append is
complete, never in between. -/
theorem impl_crash_consistency (hI : Inv P w) {h : Digest} {c : Nat} (hm : w.m.mode = .ready h c) (e : Entry) (cc : Cut) :
    entriesOf P (Impl.step P w (.append w.m.gen e (some cc))).fs.contents = entriesOf P w.fs.contents ∨
    entriesOf P (Impl.step P w (.append w.m.gen e (some cc))).fs.contents = entriesOf P w.fs.contents ++ [e] := by
  rw [impl_step_eq w hI.notBusy]
  exact crash_consistency L hI hm e cc

/-- **(e) Recovery by the driver is idempotent and settles every call in flight, once.** -/
theorem impl_reopen_idempotent (hI : Inv P w) :
    (Impl.reopen P (Impl.reopen P w)).fs = (Impl.reopen P w).fs ∧
    (Impl.reopen P (Impl.reopen P w)).m.mode = (Impl.reopen P w).m.mode := by
  have h1 := impl_reopen_eq hI
  obtain ⟨_, _, _, _, _, _, _, hI1⟩ := reopen_spec L hI
  rw [h1, impl_reopen_eq hI1]
  exact reopen_idempotent L hI

theorem impl_reopen_settles (hI : Inv P w) : ∃ E, entriesOf P w.fs.contents = E ∧
    entriesOf P (Impl.reopen P w).fs.contents = E ++ settleEntries E ∧ openCalls (E ++ settleEntries E) = [] := by
  rw [impl_reopen_eq hI]
  obtain ⟨E, h1, h2, h3, _⟩ := reopen_settles L hI
  exact ⟨E, h1, h2, h3⟩

end Lawful

/-- **(d) Fencing, of the implementation.** After a take-over no event of an older writer does anything: no effect reaches the file. -/
theorem impl_stale_append (hb : ¬ w.m.mode.isBusy) {g : Nat} (hg : g ≠ w.m.gen) (e : Entry) (cut : Option Cut) :
    Impl.step P w (.append g e cut) = w := by
  rw [impl_step_eq w hb, step_append_stale w hg]

theorem impl_stale_recover (hb : ¬ w.m.mode.isBusy) {g : Nat} (hg : g ≠ w.m.gen) (cut : Option Cut) :
    Impl.step P w (.recover g cut) = w := by
  rw [impl_step_eq w hb, step_recover_stale w hg]

theorem impl_takeOver_fences (hb : ¬ w.m.mode.isBusy) {g : Nat} (hg : g ≤ w.m.gen) (e : Entry) (cut : Option Cut) :
    Impl.step P (Impl.step P w .takeOver) (.append g e cut) = Impl.step P w .takeOver := by
  have hb1 : ¬ (Impl.step P w .takeOver).m.mode.isBusy := by
    rw [impl_step_eq w hb]; exact notBusy_step w hb _
  apply impl_stale_append hb1
  rw [impl_step_eq w hb, step_takeOver]
  simp only
  omega

end VbmJournal
