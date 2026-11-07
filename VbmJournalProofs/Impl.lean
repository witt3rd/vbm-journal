import VbmJournalProofs.Theorems
/-! # The implementation is the model (part 1: the shims' models and the plans)

The driver (`VbmJournal.Driver`) is run over the models of the shims (`VbmJournal.Sim`). This file proves what a plan does there: it performs its
effects on the file as `Fs.run` says, and a fault at an effect leaves the file a crash at that point leaves. `VbmJournalProofs.Impl` builds the
equality with the slice 1 model on it. -/
set_option linter.unusedSectionVars false

namespace VbmJournal

@[simp] theorem sim_bind {α β : Type} (x : SimM α) (f : α → SimM β) (s : Sim) :
    (x >>= f) s = match x s with
      | (Except.ok a, s') => f a s'
      | (Except.error e, s') => (Except.error e, s') := rfl

@[simp] theorem sim_pure {α : Type} (a : α) (s : Sim) : (pure a : SimM α) s = (Except.ok a, s) := rfl

theorem sim_tryCatch {α : Type} (x : SimM α) (h : String → SimM α) (s : Sim) :
    (tryCatch x h) s = match x s with
      | (Except.ok a, s') => (Except.ok a, s')
      | (Except.error e, s') => h e s' := rfl

/-- A plan that does not read. -/
def NoRead (plan : List Effect) : Prop := ∀ e ∈ plan, e ≠ Effect.readAll

theorem noRead_nil : NoRead [] := fun _ h => by simp at h

theorem noRead_cons {e : Effect} {es : List Effect} : NoRead (e :: es) ↔ e ≠ .readAll ∧ NoRead es := by
  simp [NoRead]

theorem commitPlan_noRead (cut : Option Nat) (data : Bytes) (dir : Bool) : NoRead (commitPlan cut data dir) := by
  intro e he
  simp only [commitPlan, List.mem_append] at he
  rcases he with (he | he) | he
  · cases cut <;> simp at he <;> (rcases he with rfl; simp)
  · split at he <;> simp at he <;> (rcases he with rfl | rfl <;> simp)
  · split at he <;> simp at he; rcases he with rfl; simp

/-- What one effect does in the model. -/
theorem perform_sim_nr (e : Effect) (he : e ≠ .readAll) (s : Sim) :
    Shims.sim.perform e s =
      match s.cut with
      | some c =>
        if s.done = c.n then (Except.error "cut", { s with fs := s.fs.crash c.keep c.vanish })
        else (Except.ok none, { s with fs := s.fs.run e, done := s.done + 1 })
      | none => (Except.ok none, { s with fs := s.fs.run e, done := s.done + 1 }) := by
  rcases hc : s.cut with _ | c
  · cases e <;> first | exact absurd rfl he | simp [Shims.perform, Shims.sim, simEff, hc, Fs.run]
  · by_cases hd : s.done = c.n
    · cases e <;> first | exact absurd rfl he | simp [Shims.perform, Shims.sim, simEff, hc, hd, Fs.run]
    · cases e <;> first | exact absurd rfl he | simp [Shims.perform, Shims.sim, simEff, hc, hd, Fs.run]

/-- A plan that does not read, in a model with no cut: it performs every effect on the file. -/
theorem runPlan_nocut : ∀ (plan : List Effect), NoRead plan → ∀ (s : Sim), s.cut = none →
    Shims.sim.runPlan plan s = (Except.ok none, { s with fs := s.fs.runAll plan, done := s.done + plan.length }) := by
  intro plan
  induction plan with
  | nil => intro _ s _; simp [Shims.runPlan, Fs.runAll]
  | cons e es ih =>
    intro hno s hc
    obtain ⟨he, hes⟩ := noRead_cons.1 hno
    have h1 := perform_sim_nr e he s
    simp only [hc] at h1
    simp only [Shims.runPlan, sim_bind, h1]
    rw [ih hes ⟨s.fs.run e, s.sig, none, s.done + 1⟩ rfl]
    simp [Fs.runAll, List.length_cons, Nat.add_assoc, Nat.add_comm 1, hc]

/-- A plan that does not read, in a model with a cut: if the cut is at one of its effects, the effects before it are performed, the file is what the
crash leaves, and the plan fails; otherwise the plan is performed whole. -/
theorem runPlan_cut (c : Cut) : ∀ (plan : List Effect), NoRead plan → ∀ (s : Sim), s.cut = some c →
    Shims.sim.runPlan plan s =
      if s.done ≤ c.n ∧ c.n < s.done + plan.length then
        (Except.error "cut", { s with fs := (s.fs.runPrefix (c.n - s.done) plan).crash c.keep c.vanish, done := c.n })
      else (Except.ok none, { s with fs := s.fs.runAll plan, done := s.done + plan.length }) := by
  intro plan
  induction plan with
  | nil => intro _ s _; simp [Shims.runPlan, Fs.runAll]
  | cons e es ih =>
    intro hno s hc
    obtain ⟨he, hes⟩ := noRead_cons.1 hno
    have h1 := perform_sim_nr e he s
    simp only [hc] at h1
    by_cases hd : s.done = c.n
    · simp only [hd, ite_true] at h1
      have : s.done ≤ c.n ∧ c.n < s.done + (e :: es).length := by simp; omega
      simp only [Shims.runPlan, sim_bind, h1, this, and_self, ite_true]
      simp [hd, Fs.runPrefix, hc]
    · simp only [hd, ite_false] at h1
      simp only [Shims.runPlan, sim_bind, h1]
      rw [ih hes ⟨s.fs.run e, s.sig, some c, s.done + 1⟩ rfl]
      by_cases hin : s.done ≤ c.n ∧ c.n < s.done + (e :: es).length
      · have hin' : s.done + 1 ≤ c.n ∧ c.n < s.done + 1 + es.length := by simp at hin; omega
        have hsub : c.n - s.done = (c.n - (s.done + 1)) + 1 := by omega
        rw [ite_eq_left hin', ite_eq_left hin]
        simp [hsub, Fs.runPrefix, List.take_succ_cons, hc]
      · have hin' : ¬ (s.done + 1 ≤ c.n ∧ c.n < s.done + 1 + es.length) := by simp at hin ⊢; omega
        rw [ite_eq_right hin', ite_eq_right hin]
        simp [Fs.runAll, hc, Nat.add_assoc, Nat.add_comm 1]

/-! ## The system run by the driver

`Impl.step P w ev` is one event of the system, run by the driver over the models of the shims: the machine state is the driver's, the file the
model's. A cut is a fault of the model at the `n`-th effect; if the plan finishes before it, the crash comes after the plan (as in `World.finish`). -/

def isReady : Mode → Bool
  | .ready _ _ => true
  | _ => false

/-- One event of the writer, run by the driver over the models of the shims, from the system `w`. -/
def Impl.run (P : Params) (w : World) (e : Event) (cut : Option Cut) : World :=
  match drive P Shims.sim w.m e ⟨w.fs, none, cut, 0⟩ with
  | (Except.ok (st', some _), s') => ⟨st', s'.fs⟩
  | (Except.ok (st', none), s') =>
    match cut with
    | some c => if st' ≠ w.m ∧ isReady st'.mode then ⟨(step P st' .crash).1, s'.fs.crash c.keep c.vanish⟩ else ⟨st', s'.fs⟩
    | none => ⟨st', s'.fs⟩
  | (Except.error _, s') => ⟨(step P w.m .crash).1, s'.fs⟩

/-- One event of the system with the driver as the writer; `crash` is the environment's. -/
def Impl.step (P : Params) (w : World) : WEvent → World
  | .takeOver => Impl.run P w .takeOver none
  | .crash k v => ⟨(VbmJournal.step P w.m .crash).1, w.fs.crash k v⟩
  | .recover g cut => Impl.run P w (.recover g) cut
  | .append g e cut => Impl.run P w (.append g e) cut

variable {P : Params}

theorem drive_eq (st : St) (ev : Event) (s : Sim) :
    drive P Shims.sim st ev s = match driveRaw P Shims.sim (fun _ => pure ()) st ev s with
      | (Except.ok st', s') => (Except.ok (st', none), s')
      | (Except.error e, s') => (Except.ok ((step P st .crash).1, some e), s') := by
  simp only [drive, guarded, sim_tryCatch, sim_bind, sim_pure]
  rcases driveRaw P Shims.sim (fun _ => pure ()) st ev s with ⟨r, s'⟩
  cases r <;> rfl

theorem runPlan_ok_none (plan : List Effect) (hno : NoRead plan) (s : Sim) (r : Option Bytes) (s' : Sim)
    (h : Shims.sim.runPlan plan s = (Except.ok r, s')) : r = none := by
  rcases hc : s.cut with _ | c
  · rw [runPlan_nocut plan hno s hc] at h; simp at h; exact h.1.symm
  · rw [runPlan_cut c plan hno s hc] at h
    split at h <;> simp at h; exact h.1.symm

theorem ack_notBusy (st : St) (h : ¬ st.mode.isBusy) : ack P st = st := by
  simp [ack, h]

/-- A refused event: nothing is performed, the state stays. -/
theorem drive_refused (st : St) (ev : Event) (hst : step P st ev = (st, [])) (hb : ¬ st.mode.isBusy) (s : Sim) :
    drive P Shims.sim st ev s = (Except.ok (st, none), s) := by
  rw [drive_eq]
  simp [driveRaw, hst, Shims.runPlan, ack_notBusy st hb]

/-- An event whose plan does not read: the plan is performed (or the fault comes), then acknowledged. -/
theorem drive_planned (st ev : _) (st1 : St) (plan : List Effect) (hst : step P st ev = (st1, plan)) (hno : NoRead plan)
    (fs : Fs) (sig : Option Bytes) (cut : Option Cut) :
    drive P Shims.sim st ev ⟨fs, sig, cut, 0⟩ =
      match cut with
      | none => (Except.ok (ack P st1, none), ⟨fs.runAll plan, sig, none, plan.length⟩)
      | some c =>
        if c.n < plan.length then
          (Except.ok ((step P st .crash).1, some "cut"), ⟨(fs.runPrefix c.n plan).crash c.keep c.vanish, sig, some c, c.n⟩)
        else (Except.ok (ack P st1, none), ⟨fs.runAll plan, sig, some c, plan.length⟩) := by
  rw [drive_eq]
  cases cut with
  | none =>
    simp [driveRaw, hst, runPlan_nocut plan hno ⟨fs, sig, none, 0⟩ rfl]
  | some c =>
    have h := runPlan_cut c plan hno ⟨fs, sig, some c, 0⟩ rfl
    by_cases hin : c.n < plan.length
    · simp [driveRaw, hst, h, hin]
    · simp [driveRaw, hst, h, hin]

theorem recoverPlan_noRead (st : St) (bytes : Bytes) : NoRead (recoverPlan P st bytes).2 := by
  unfold recoverPlan
  cases read P bytes with
  | none => exact noRead_nil
  | some r =>
    simp only
    split
    · exact noRead_nil
    · exact commitPlan_noRead (some (bytes.length - r.tail.length)) (encodeFrom P r.head (settleEntries r.entries)) true

theorem runPlan_readAll (s : Sim) : Shims.sim.runPlan [.readAll] s = (Except.ok (some s.fs.contents), s) := rfl

/-- Recovery of a writer that has just taken over: the file is read, the machine's plan is performed (or the fault comes), then acknowledged. -/
theorem drive_recover (st : St) (hm : st.mode = .opened) (fs : Fs) (sig : Option Bytes) (cut : Option Cut) :
    match recoverPlan P ⟨st.gen, .reading⟩ fs.contents with
    | (m2, plan) =>
      drive P Shims.sim st (.recover st.gen) ⟨fs, sig, cut, 0⟩ =
        match cut with
        | none => (Except.ok (ack P m2, none), ⟨fs.runAll plan, sig, none, plan.length⟩)
        | some c =>
          if c.n < plan.length then
            (Except.ok ((step P st .crash).1, some "cut"), ⟨(fs.runPrefix c.n plan).crash c.keep c.vanish, sig, some c, c.n⟩)
          else (Except.ok (ack P m2, none), ⟨fs.runAll plan, sig, some c, plan.length⟩) := by
  obtain ⟨gen, mode⟩ := st
  simp only at hm
  subst hm
  rcases hr : recoverPlan P ⟨gen, .reading⟩ fs.contents with ⟨m2, plan⟩
  have hno : NoRead plan := by have := recoverPlan_noRead (P := P) ⟨gen, .reading⟩ fs.contents; rw [hr] at this; exact this
  simp only
  rw [drive_eq]
  cases cut with
  | none =>
    simp [driveRaw, step, runPlan_readAll, hr, runPlan_nocut plan hno ⟨fs, sig, none, 0⟩ rfl]
  | some c =>
    have h := runPlan_cut c plan hno ⟨fs, sig, some c, 0⟩ rfl
    by_cases hin : c.n < plan.length
    · simp [driveRaw, step, runPlan_readAll, hr, h, hin]
    · simp [driveRaw, step, runPlan_readAll, hr, h, hin]

/-! ## One event, by cases -/

theorem runPrefix_all (f : Fs) (plan : List Effect) (n : Nat) (h : plan.length ≤ n) : f.runPrefix n plan = f.runAll plan := by
  simp [Fs.runPrefix, Fs.runAll, List.take_of_length_le h]

theorem ack_busy (m : St) (hb : m.mode.isBusy) : isReady (ack P m).mode = true ∧ (ack P m).gen = m.gen := by
  obtain ⟨gen, mode⟩ := m
  cases mode <;> simp [Mode.isBusy] at hb
  simp [ack, Mode.isBusy, step, isReady]

theorem recoverPlan_gen (st : St) (bytes : Bytes) : (recoverPlan P st bytes).1.gen = st.gen := by
  unfold recoverPlan
  cases read P bytes with
  | none => rfl
  | some r => simp only; split <;> rfl

theorem recoverPlan_notBusy (st : St) (bytes : Bytes) (h : ¬ (recoverPlan P st bytes).1.mode.isBusy) :
    (recoverPlan P st bytes).2 = [] ∧ (recoverPlan P st bytes).1.mode = .broken := by
  unfold recoverPlan at h ⊢
  cases hr : read P bytes with
  | none => simp
  | some r =>
    rw [hr] at h
    simp only at h ⊢
    split at h <;> simp [Mode.isBusy] at h

theorem step_append_refused (st : St) (g : Nat) (e : Entry) (h : g ≠ st.gen ∨ ∀ h c, st.mode ≠ .ready h c) :
    step P st (.append g e) = (st, []) := by
  obtain ⟨gen, mode⟩ := st
  rcases h with h | h
  · simp [step, h]
  · cases mode with
    | ready hh c => exact absurd rfl (h hh c)
    | _ => simp [step]

theorem step_recover_refused (st : St) (g : Nat) (h : g ≠ st.gen ∨ st.mode ≠ .opened) : step P st (.recover g) = (st, []) := by
  obtain ⟨gen, mode⟩ := st
  rcases h with h | h
  · simp [step, h]
  · cases mode with
    | opened => exact absurd rfl h
    | _ => simp [step]

theorem impl_takeOver (w : World) : Impl.step P w .takeOver = World.step P w .takeOver := by
  have hst : step P w.m .takeOver = (⟨w.m.gen + 1, .opened⟩, []) := by simp [step]
  have h := drive_planned (P := P) w.m .takeOver _ _ hst noRead_nil w.fs none none
  simp only [Impl.step, Impl.run]
  rw [show (⟨w.fs, none, none, 0⟩ : Sim) = ⟨w.fs, none, none, 0⟩ from rfl, h]
  simp [ack, Mode.isBusy, step_takeOver, Fs.runAll]

theorem impl_crash (w : World) (k : Nat) (v : Bool) : Impl.step P w (.crash k v) = World.step P w (.crash k v) := by
  simp [Impl.step, step_crash, crash_idle]

theorem impl_refused_append (w : World) (hb : ¬ w.m.mode.isBusy) (g : Nat) (e : Entry) (cut : Option Cut)
    (hr : step P w.m (.append g e) = (w.m, [])) (hw : World.step P w (.append g e cut) = w) :
    Impl.step P w (.append g e cut) = World.step P w (.append g e cut) := by
  rw [hw]
  simp only [Impl.step, Impl.run]
  rw [drive_refused _ _ hr hb]
  cases cut <;> simp

theorem impl_append (w : World) (hb : ¬ w.m.mode.isBusy) (g : Nat) (e : Entry) (cut : Option Cut) :
    Impl.step P w (.append g e cut) = World.step P w (.append g e cut) := by
  by_cases hg : g = w.m.gen
  · by_cases hrd : ∃ h c, w.m.mode = .ready h c
    · obtain ⟨h, c, hm⟩ := hrd
      subst hg
      have hst : step P w.m (.append w.m.gen e) =
          (⟨w.m.gen, .busy (P.link h (P.enc e)) (c + 1)⟩, commitPlan none (encodeFrom P h [e]) (c == 0)) := by
        simp [step, hm]
      rw [step_append_ready w hm e cut]
      simp only [Impl.step, Impl.run]
      rw [drive_planned _ _ _ _ hst (commitPlan_noRead _ _ _) w.fs none cut]
      have hack := acked_busy (P := P) w.m.gen (P.link h (P.enc e)) (c + 1)
      have hack' : ack P (⟨w.m.gen, .busy (P.link h (P.enc e)) (c + 1)⟩ : St) = ⟨w.m.gen, .ready (P.link h (P.enc e)) (c + 1)⟩ := by
        simp [ack, Mode.isBusy, hack]
      cases cut with
      | none => simp [hack', finish_none, hack, Fs.runAll]
      | some cc =>
        by_cases hin : cc.n < (commitPlan none (encodeFrom P h [e]) (c == 0)).length
        · simp [hin, finish_some, crash_idle]
        · have hne : (⟨w.m.gen, .ready (P.link h (P.enc e)) (c + 1)⟩ : St) ≠ w.m := fun heq => by
            have := congrArg (fun m : St => m.mode) heq
            simp [hm] at this
          simp [hin, hack', hne, isReady, finish_some, crash_idle, runPrefix_all _ _ _ (Nat.not_lt.1 hin)]
    · have hr := step_append_refused (P := P) w.m g e (Or.inr (fun h c hh => hrd ⟨h, c, hh⟩))
      exact impl_refused_append w hb g e cut hr (step_append_other w g e cut (fun h c hh => hrd ⟨h, c, hh⟩))
  · exact impl_refused_append w hb g e cut (step_append_refused (P := P) w.m g e (Or.inl hg)) (step_append_stale w hg e cut)

theorem impl_refused_recover (w : World) (hb : ¬ w.m.mode.isBusy) (g : Nat) (cut : Option Cut)
    (hr : step P w.m (.recover g) = (w.m, [])) (hw : World.step P w (.recover g cut) = w) :
    Impl.step P w (.recover g cut) = World.step P w (.recover g cut) := by
  rw [hw]
  simp only [Impl.step, Impl.run]
  rw [drive_refused _ _ hr hb]
  cases cut <;> simp

theorem impl_recover (w : World) (hb : ¬ w.m.mode.isBusy) (g : Nat) (cut : Option Cut) :
    Impl.step P w (.recover g cut) = World.step P w (.recover g cut) := by
  by_cases hg : g = w.m.gen
  · by_cases hm : w.m.mode = .opened
    · subst hg
      rw [step_recover_opened w hm cut]
      have hd := drive_recover (P := P) w.m hm w.fs none cut
      simp only [Impl.step, Impl.run]
      rcases hr : recoverPlan P ⟨w.m.gen, .reading⟩ w.fs.contents with ⟨m2, plan⟩
      rw [hr] at hd
      simp only at hd ⊢
      rw [hd]
      have hg2 : m2.gen = w.m.gen := by
        have := recoverPlan_gen (P := P) ⟨w.m.gen, .reading⟩ w.fs.contents
        rw [hr] at this; exact this
      by_cases hbz : m2.mode.isBusy
      · obtain ⟨hrd, hgk⟩ := ack_busy (P := P) m2 hbz
        have hne : ack P m2 ≠ w.m := fun heq => by
          rw [heq, hm] at hrd
          simp [isReady] at hrd
        have hcr : (step P (ack P m2) .crash).1 = (step P m2 .crash).1 := by
          simp [crash_idle, hgk]
        simp only [hbz, ite_true]
        cases cut with
        | none => simp [finish_none, ack, hbz, Fs.runAll]
        | some cc =>
          by_cases hin : cc.n < plan.length
          · simp [hin, finish_some, crash_idle, hg2]
          · simp [hin, hrd, hne, finish_some, hcr, runPrefix_all _ _ _ (Nat.not_lt.1 hin)]
      · obtain ⟨hp, hbk⟩ := recoverPlan_notBusy (P := P) ⟨w.m.gen, .reading⟩ w.fs.contents (by rw [hr]; exact hbz)
        rw [hr] at hp hbk
        simp only at hp hbk
        subst hp
        have hack : ack P m2 = m2 := ack_notBusy m2 hbz
        simp only [hbz]
        cases cut with
        | none => simp [hack, Fs.runAll]
        | some cc => simp [hack, hbk, isReady, Fs.runAll]
    · exact impl_refused_recover w hb g cut (step_recover_refused (P := P) w.m g (Or.inr hm)) (step_recover_other w g cut hm)
  · exact impl_refused_recover w hb g cut (step_recover_refused (P := P) w.m g (Or.inl hg)) (step_recover_stale w hg cut)

/-! ## The theorem -/

theorem notBusy_finish (w : World) (m1 : St) (plan : List Effect) (cut : Option Cut) (hb : m1.mode.isBusy) :
    ¬ (w.finish P m1 plan cut).m.mode.isBusy := by
  obtain ⟨gen, mode⟩ := m1
  cases mode <;> simp [Mode.isBusy] at hb
  cases cut <;> simp [finish_none, finish_some, step, Mode.isBusy]

/-- The machine is never waiting for a plan between events. -/
theorem notBusy_step (w : World) (hb : ¬ w.m.mode.isBusy) (ev : WEvent) : ¬ (World.step P w ev).m.mode.isBusy := by
  cases ev with
  | takeOver => simp [step_takeOver, Mode.isBusy]
  | crash k v => simp [step_crash, Mode.isBusy]
  | append g e cut =>
    by_cases hg : g = w.m.gen
    · by_cases hrd : ∃ h c, w.m.mode = .ready h c
      · obtain ⟨h, c, hm⟩ := hrd
        subst hg
        rw [step_append_ready w hm e cut]
        exact notBusy_finish w _ _ cut (by simp [Mode.isBusy])
      · rw [step_append_other w g e cut (fun h c hh => hrd ⟨h, c, hh⟩)]; exact hb
    · rw [step_append_stale w hg]; exact hb
  | recover g cut =>
    by_cases hg : g = w.m.gen
    · by_cases hm : w.m.mode = .opened
      · subst hg
        rw [step_recover_opened w hm cut]
        rcases hr : recoverPlan P ⟨w.m.gen, .reading⟩ w.fs.contents with ⟨m2, plan⟩
        simp only
        by_cases hbz : m2.mode.isBusy
        · simp only [hbz, ite_true]; exact notBusy_finish w m2 plan cut hbz
        · simp only [hbz]; exact hbz
      · rw [step_recover_other w g cut hm]; exact hb
    · rw [step_recover_stale w hg]; exact hb

/-- **The implementation is the model, one event at a time.** One event of the system run by the driver over the models of the shims
(`Impl.step`) is the event of the slice 1 model (`World.step`), for every event, every crash point, and every system the machine is not waiting
in. -/
theorem impl_step_eq (w : World) (hb : ¬ w.m.mode.isBusy) (ev : WEvent) : Impl.step P w ev = World.step P w ev := by
  cases ev with
  | takeOver => exact impl_takeOver w
  | crash k v => exact impl_crash w k v
  | append g e cut => exact impl_append w hb g e cut
  | recover g cut => exact impl_recover w hb g cut

/-- A list of events run by the driver. -/
def Impl.runAll (P : Params) (w : World) (evs : List WEvent) : World := evs.foldl (Impl.step P) w

/-- **The implementation is the model, step for step.** Any list of events, from any system the machine is not waiting in, run by the driver
over the models of the shims, gives the system the slice 1 model gives. -/
theorem impl_run_eq (evs : List WEvent) : ∀ (w : World), ¬ w.m.mode.isBusy → Impl.runAll P w evs = World.run P w evs := by
  induction evs with
  | nil => intro w _; rfl
  | cons ev evs ih =>
    intro w hb
    simp only [Impl.runAll, World.run, List.foldl_cons] at ih ⊢
    rw [impl_step_eq w hb ev]
    exact ih _ (notBusy_step w hb ev)

/-- From the start. -/
theorem impl_reachable (evs : List WEvent) : Impl.runAll P World.init evs = World.run P World.init evs :=
  impl_run_eq evs _ (by simp [World.init, St.init, Mode.isBusy])

end VbmJournal
