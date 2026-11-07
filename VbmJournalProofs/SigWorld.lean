import VbmJournalProofs.SigImpl
/-! # The signature of a journal stays honest, through every crash

The signed driver (`driveSigned`) runs over the model with the signature file as part of the system: `SWorld` is a `World` and the signature file,
`SImpl.step` one event of it (the driver as the writer, the crash points as in slice 1). `SigHonest` says what the signature file holds is the signature
of a prefix of the journal.

**Plain statement.** `signed_step`: from a system whose journal is a journal (`Inv`) and whose signature is honest, any event, with any crash point,
leaves (1) **the journal as the slice 1 model leaves it** (`World.step`: so every theorem of slice 1 holds of the signed driver too), (2) a signature
that is honest, so the verifier accepts the journal against it, with the records after the signed point as the unsigned tail (`signed_reachable`,
`verdict_honest`). Honesty is kept through every crash: the signature is written only after the records it signs are durable, and a journal only grows
(`append_only`), so a signed prefix is always a prefix of what is left. -/
set_option linter.unusedSectionVars false

namespace VbmJournal

variable {P : Params} {mac : Nat → Digest → Bytes}

/-- The system and the signature file. -/
structure SWorld where
  w : World
  sig : Option Bytes

/-- No signature file; or the signature of a prefix of the journal, whose directory entry is durable. -/
def SigHonest (P : Params) (mac : Nat → Digest → Bytes) (w : World) (sig : Option Bytes) : Prop :=
  sig = none ∨ ∃ i, 0 < i ∧ w.fs.dirSafe = true ∧ i ≤ (entriesOf P w.fs.contents).length ∧
    sig = some (Sig.make mac i (headFrom P P.genesis ((entriesOf P w.fs.contents).take i))).toBytes

section Lawful
variable (L : P.Lawful)
include L

/-- A journal only grows, so a signature of a prefix stays the signature of a prefix. -/
theorem honest_mono {w w' : World} {sig : Option Bytes} (hpre : World.records P w <+: World.records P w')
    (h : SigHonest P mac w sig) : SigHonest P mac w' sig := by
  rcases h with h | ⟨i, hi0, hdir, hle, hsig⟩
  · exact Or.inl h
  · right
    have hrec : World.records P w = entriesOf P w.fs.contents := by simp [World.records, hdir]
    have hdir' : w'.fs.dirSafe = true := by
      cases hd : w'.fs.dirSafe
      · exfalso
        have : World.records P w' = [] := by simp [World.records, hd]
        rw [this] at hpre
        have := List.prefix_nil.1 hpre
        rw [hrec] at this
        rw [this] at hle
        simp at hle; omega
      · rfl
    have hrec' : World.records P w' = entriesOf P w'.fs.contents := by simp [World.records, hdir']
    rw [hrec, hrec'] at hpre
    obtain ⟨t, ht⟩ := hpre
    have hle' : i ≤ (entriesOf P w'.fs.contents).length := by
      rw [← ht]; simp; omega
    have htake : (entriesOf P w'.fs.contents).take i = (entriesOf P w.fs.contents).take i := by
      rw [← ht]; exact List.take_append_of_le_length hle
    exact ⟨i, hi0, hdir', hle', by rw [htake]; exact hsig⟩

/-- An honest signature passes the signature gate of recovery. -/
theorem honest_gate {w : World} (hI : Inv P w) {sig : Option Bytes} (h : SigHonest P mac w sig) :
    gateMsg P mac sig w.fs.contents = none := by
  obtain ⟨r, hr⟩ := hI.readable
  have hent : entriesOf P w.fs.contents = r.entries := by simp [entriesOf, hr]
  unfold gateMsg
  rw [hr]
  simp only
  rcases h with rfl | ⟨i, hi0, hdir, hle, hsig⟩
  · simp [verdict_none]
  · rw [hent] at hle hsig
    have hlen : (r.entries.take i).length = i := by simp; omega
    have hsp : sp ∉ headFrom P P.genesis (r.entries.take i) :=
      headFrom_clean L (by intro h0; rw [h0] at hlen; simp at hlen; omega)
    rw [hsig, verdict_honest (P := P) (mac := mac) hle hsp]

end Lawful

/-! ## The signed system -/

/-- One event of the writer, run by the signed driver over the models of the shims, from the system `sw`. -/
def SImpl.run (P : Params) (mac : Nat → Digest → Bytes) (sw : SWorld) (e : Event) (cut : Option Cut) : SWorld :=
  match driveSigned P mac Shims.sim sw.w.m e ⟨sw.w.fs, sw.sig, cut, 0⟩ with
  | (Except.ok (st', some _), s') => ⟨⟨st', s'.fs⟩, s'.sig⟩
  | (Except.ok (st', none), s') =>
    match cut with
    | some c =>
      if st' ≠ sw.w.m ∧ isReady st'.mode then ⟨⟨(step P st' .crash).1, s'.fs.crash c.keep c.vanish⟩, s'.sig⟩ else ⟨⟨st', s'.fs⟩, s'.sig⟩
    | none => ⟨⟨st', s'.fs⟩, s'.sig⟩
  | (Except.error _, s') => ⟨⟨(step P sw.w.m .crash).1, s'.fs⟩, s'.sig⟩

/-- One event of the signed system; `crash` is the environment's (the signature file is not touched). -/
def SImpl.step (P : Params) (mac : Nat → Digest → Bytes) (sw : SWorld) : WEvent → SWorld
  | .takeOver => SImpl.run P mac sw .takeOver none
  | .crash k v => ⟨⟨(VbmJournal.step P sw.w.m .crash).1, sw.w.fs.crash k v⟩, sw.sig⟩
  | .recover g cut => SImpl.run P mac sw (.recover g) cut
  | .append g e cut => SImpl.run P mac sw (.append g e) cut

/-- If the signed driver's result is the unsigned one's with another signature file, the signed system's journal is the unsigned one's. -/
theorem simpl_run_of (sw : SWorld) (e : Event) (cut : Option Cut) (r : Except String (St × Option String)) (s' : Sim) (X : Option Bytes)
    (hd : drive P Shims.sim sw.w.m e ⟨sw.w.fs, none, cut, 0⟩ = (r, s'))
    (hs : driveSigned P mac Shims.sim sw.w.m e ⟨sw.w.fs, sw.sig, cut, 0⟩ = (r, { s' with sig := X })) :
    SImpl.run P mac sw e cut = ⟨Impl.run P sw.w e cut, X⟩ := by
  unfold SImpl.run Impl.run
  rw [hd, hs]
  rcases r with _ | ⟨st', _ | m⟩
  · rfl
  · cases cut with
    | none => rfl
    | some c => by_cases hc : st' ≠ sw.w.m ∧ isReady st'.mode = true <;> simp [hc]
  · rfl

/-- The signature file after an event whose plan does not read: unchanged if it fails, signed at the head it leaves if it completes. -/
def planSig (P : Params) (mac : Nat → Digest → Bytes) (st st1 : St) (plan : List Effect) (sig : Option Bytes) : Option Cut → Option Bytes
  | none => if ack P st1 ≠ st then signSig mac (ack P st1) sig else sig
  | some c => if c.n < plan.length then sig else if ack P st1 ≠ st then signSig mac (ack P st1) sig else sig

theorem simpl_planned (sw : SWorld) (ev : Event) (st1 : St) (plan : List Effect) (hst : step P sw.w.m ev = (st1, plan)) (hno : NoRead plan)
    (cut : Option Cut) :
    SImpl.run P mac sw ev cut = ⟨Impl.run P sw.w ev cut, planSig P mac sw.w.m st1 plan sw.sig cut⟩ := by
  cases cut with
  | none =>
    exact simpl_run_of sw ev none _ _ _ (drive_planned _ _ _ _ hst hno sw.w.fs none none)
      (by rw [driveSigned_planned _ _ _ _ hst hno]; rfl)
  | some c =>
    have h1 := drive_planned (P := P) _ _ _ _ hst hno sw.w.fs none (some c)
    have h2 := driveSigned_planned (P := P) (mac := mac) _ _ _ _ hst hno sw.w.fs sw.sig (some c)
    dsimp only at h1 h2
    by_cases hin : c.n < plan.length
    · rw [ite_eq_left hin] at h1 h2
      exact simpl_run_of sw ev (some c) _ _ _ h1 (by rw [h2]; simp [planSig, hin])
    · rw [ite_eq_right hin] at h1 h2
      exact simpl_run_of sw ev (some c) _ _ _ h1 (by rw [h2]; simp [planSig, hin])

/-- The signature file after a signed recovery of a journal whose signature holds. -/
def recSig (P : Params) (mac : Nat → Digest → Bytes) (m2 : St) (plan : List Effect) (sig : Option Bytes) : Option Cut → Option Bytes
  | none => signSig mac (ack P m2) sig
  | some c => if c.n < plan.length then sig else signSig mac (ack P m2) sig

theorem simpl_recover (sw : SWorld) (hm : sw.w.m.mode = .opened) (hg : gateMsg P mac sw.sig sw.w.fs.contents = none) (cut : Option Cut) :
    match recoverPlan P ⟨sw.w.m.gen, .reading⟩ sw.w.fs.contents with
    | (m2, plan) => SImpl.run P mac sw (.recover sw.w.m.gen) cut = ⟨Impl.run P sw.w (.recover sw.w.m.gen) cut, recSig P mac m2 plan sw.sig cut⟩ := by
  have h1 := drive_recover (P := P) sw.w.m hm sw.w.fs none cut
  have h2 := driveSigned_recover (P := P) (mac := mac) sw.w.m hm sw.w.fs sw.sig cut
  rcases hr : recoverPlan P ⟨sw.w.m.gen, .reading⟩ sw.w.fs.contents with ⟨m2, plan⟩
  rw [hr] at h1 h2
  simp only [hg] at h2
  simp only
  cases cut with
  | none =>
    exact simpl_run_of sw _ none _ _ _ h1 (by rw [h2]; rfl)
  | some c =>
    dsimp only at h1 h2
    by_cases hin : c.n < plan.length
    · rw [ite_eq_left hin] at h1 h2
      exact simpl_run_of sw _ (some c) _ _ _ h1 (by rw [h2]; simp [recSig, hin])
    · rw [ite_eq_right hin] at h1 h2
      exact simpl_run_of sw _ (some c) _ _ _ h1 (by rw [h2]; simp [recSig, hin])

section Lawful
variable (L : P.Lawful)
include L

/-- The signature of a ready writer's head is honest for any system whose file is the writer's (contents and directory entry). -/
theorem honest_of_ready {w0 w' : World} (hI0 : Inv P w0) {h : Digest} {c : Nat} (hm : w0.m.mode = .ready h c) (hc : c ≠ 0)
    (hc1 : w'.fs.contents = w0.fs.contents) (hc2 : w'.fs.dirSafe = w0.fs.dirSafe) :
    SigHonest P mac w' (some (Sig.make mac c h).toBytes) := by
  obtain ⟨r, hr, htail, hlen, hdir, hdur, hh⟩ := ready_facts L hI0 hm
  have hent : entriesOf P w'.fs.contents = r.entries := by simp [entriesOf, hc1, hr]
  have hdir' : w0.fs.dirSafe = true := by rcases hdir with hd | hd; exact hd; exact absurd hd hc
  right
  refine ⟨c, by omega, by rw [hc2]; exact hdir', by rw [hent]; omega, ?_⟩
  rw [hent, List.take_of_length_le (by omega), ← hh]

omit L in
/-- A crash after a file that is synced and whose directory entry is durable leaves it as it is. -/
theorem crash_same {f : Fs} (hp : f.pending = []) (hd : f.dirSafe = true) (k : Nat) (v : Bool) : f.crash k v = f := by
  rcases crash_cases f hp k v with h | ⟨_, h⟩
  · exact h
  · rw [hd] at h; exact absurd h (by simp)

omit L in
/-- An event whose plan is empty does not touch the signature. -/
theorem planSig_nil (st st1 : St) (sig : Option Bytes) (cut : Option Cut)
    (h : ack P st1 ≠ st → signSig mac (ack P st1) sig = sig) : planSig P mac st st1 [] sig cut = sig := by
  cases cut with
  | none =>
    by_cases hc : ack P st1 ≠ st
    · simp [planSig, hc, h hc]
    · simp [planSig, hc]
  | some c =>
    by_cases hc : ack P st1 ≠ st
    · simp [planSig, hc, h hc]
    · simp [planSig, hc]

/-- A plan that completes (and a crash after it, if any) leaves the signature of the ready head honest. -/
theorem honest_finish (w : World) (m1 : St) (plan : List Effect) (hI0 : Inv P (w.finish P m1 plan none)) {h : Digest} {c : Nat}
    (hm0 : (w.finish P m1 plan none).m.mode = .ready h c) (hc : c ≠ 0) (cut : Option Cut)
    (hcut : ∀ cc, cut = some cc → plan.length ≤ cc.n) :
    SigHonest P mac (w.finish P m1 plan cut) (some (Sig.make mac c h).toBytes) := by
  cases cut with
  | none => exact honest_of_ready L hI0 hm0 hc rfl rfl
  | some cc =>
    have hn := hcut cc rfl
    obtain ⟨r, hr, htail, hlen, hdir, hdur, hh⟩ := ready_facts L hI0 hm0
    have hdir' : (w.finish P m1 plan none).fs.dirSafe = true := by rcases hdir with hd | hd; exact hd; exact absurd hd hc
    have hsame := crash_same (k := cc.keep) (v := cc.vanish) hI0.pending hdir'
    refine honest_of_ready L hI0 hm0 hc ?_ ?_
    · rw [finish_some, runPrefix_all _ _ _ hn]; simp only [finish_none] at hsame ⊢; rw [hsame]
    · rw [finish_some, runPrefix_all _ _ _ hn]; simp only [finish_none] at hsame ⊢; rw [hsame]

omit L in
/-- A refused event, signed: nothing changes, the signature neither. -/
theorem simpl_refused (sw : SWorld) (ev : Event) (hb : ¬ sw.w.m.mode.isBusy) (hst : step P sw.w.m ev = (sw.w.m, [])) (cut : Option Cut) :
    SImpl.run P mac sw ev cut = ⟨Impl.run P sw.w ev cut, sw.sig⟩ := by
  rw [simpl_planned sw ev _ _ hst noRead_nil cut]
  rw [planSig_nil _ _ _ _ (by intro h; exact absurd (ack_notBusy sw.w.m hb) h)]

/-- **One event of the signed system.** From a journal whose signature is honest, any event with any crash point leaves the journal the slice 1
model leaves, and a signature that is honest. -/
theorem signed_step {w : World} {sig : Option Bytes} (hI : Inv P w) (hs : SigHonest P mac w sig) (ev : WEvent) :
    (SImpl.step P mac ⟨w, sig⟩ ev).w = World.step P w ev ∧
    SigHonest P mac (World.step P w ev) (SImpl.step P mac ⟨w, sig⟩ ev).sig := by
  have hb := hI.notBusy
  have hinv := inv_step L hI ev
  have hmono := honest_mono (mac := mac) L hinv.2 hs
  cases ev with
  | takeOver =>
    have hst : step P w.m .takeOver = (⟨w.m.gen + 1, .opened⟩, []) := by simp [step]
    have h := simpl_planned (mac := mac) ⟨w, sig⟩ .takeOver _ _ hst noRead_nil none
    have hs' : planSig P mac w.m ⟨w.m.gen + 1, .opened⟩ [] sig none = sig :=
      planSig_nil _ _ _ _ (by intro _; simp [ack, Mode.isBusy, signSig])
    show (SImpl.run P mac ⟨w, sig⟩ .takeOver none).w = _ ∧ SigHonest P mac _ (SImpl.run P mac ⟨w, sig⟩ .takeOver none).sig
    rw [h]
    simp only [hs']
    exact ⟨impl_step_eq (P := P) w hb .takeOver, hmono⟩
  | crash k v =>
    refine ⟨?_, ?_⟩
    · exact impl_step_eq (P := P) w hb (.crash k v)
    · exact hmono
  | append g e cut =>
    by_cases hg : g = w.m.gen
    · by_cases hrd : ∃ h c, w.m.mode = .ready h c
      · obtain ⟨h, c, hm⟩ := hrd
        subst hg
        have hst : step P w.m (.append w.m.gen e) =
            (⟨w.m.gen, .busy (P.link h (P.enc e)) (c + 1)⟩, commitPlan none (encodeFrom P h [e]) (c == 0)) := by
          simp [step, hm]
        have h1 := simpl_planned (mac := mac) ⟨w, sig⟩ (.append w.m.gen e) _ _ hst (commitPlan_noRead _ _ _) cut
        have hw := impl_step_eq (P := P) w hb (.append w.m.gen e cut)
        show (SImpl.run P mac ⟨w, sig⟩ (.append w.m.gen e) cut).w = _ ∧
          SigHonest P mac _ (SImpl.run P mac ⟨w, sig⟩ (.append w.m.gen e) cut).sig
        rw [h1]
        refine ⟨hw, ?_⟩
        have hack : ack P (⟨w.m.gen, .busy (P.link h (P.enc e)) (c + 1)⟩ : St) =
            ⟨w.m.gen, .ready (P.link h (P.enc e)) (c + 1)⟩ := by simp [ack, Mode.isBusy, step]
        have hne : (⟨w.m.gen, .ready (P.link h (P.enc e)) (c + 1)⟩ : St) ≠ w.m := fun heq => by
          have := congrArg (fun m : St => m.mode) heq
          simp [hm] at this
        have hsig : signSig mac (ack P (⟨w.m.gen, .busy (P.link h (P.enc e)) (c + 1)⟩ : St)) sig =
            some (Sig.make mac (c + 1) (P.link h (P.enc e))).toBytes := by simp [signSig, hack]
        have hw0 : World.step P w (.append w.m.gen e none) =
            World.finish P w ⟨w.m.gen, .busy (P.link h (P.enc e)) (c + 1)⟩ (commitPlan none (encodeFrom P h [e]) (c == 0)) none := by
          rw [step_append_ready w hm]
        have hI0 : Inv P (World.finish P w ⟨w.m.gen, .busy (P.link h (P.enc e)) (c + 1)⟩ (commitPlan none (encodeFrom P h [e]) (c == 0)) none) := by
          rw [← hw0]; exact (inv_step L hI _).1
        have hm0 : (World.finish P w ⟨w.m.gen, .busy (P.link h (P.enc e)) (c + 1)⟩ (commitPlan none (encodeFrom P h [e]) (c == 0)) none).m.mode =
            .ready (P.link h (P.enc e)) (c + 1) := by
          rw [finish_none, acked_busy]
        cases cut with
        | none =>
          simp only [planSig, hack, hne, ne_eq, not_false_eq_true, ite_true] at hsig ⊢
          rw [hsig, step_append_ready w hm]
          exact honest_finish L w _ _ hI0 hm0 (by omega) none (by simp)
        | some cc =>
          by_cases hin : cc.n < (commitPlan none (encodeFrom P h [e]) (c == 0)).length
          · simp only [planSig, hin, ite_true]
            exact hmono
          · simp only [planSig, hin, ite_false, hack, hne, ne_eq, not_false_eq_true, ite_true] at hsig ⊢
            rw [hsig, step_append_ready w hm]
            exact honest_finish L w _ _ hI0 hm0 (by omega) (some cc) (by intro cc' hc; cases hc; exact Nat.not_lt.1 hin)
      · have hr := step_append_refused (P := P) w.m g e (Or.inr (fun h c hh => hrd ⟨h, c, hh⟩))
        have h1 := simpl_refused (mac := mac) ⟨w, sig⟩ (.append g e) hb hr cut
        have hw := impl_step_eq (P := P) w hb (.append g e cut)
        show (SImpl.run P mac ⟨w, sig⟩ (.append g e) cut).w = _ ∧ SigHonest P mac _ (SImpl.run P mac ⟨w, sig⟩ (.append g e) cut).sig
        rw [h1]
        exact ⟨hw, hmono⟩
    · have hr := step_append_refused (P := P) w.m g e (Or.inl hg)
      have h1 := simpl_refused (mac := mac) ⟨w, sig⟩ (.append g e) hb hr cut
      have hw := impl_step_eq (P := P) w hb (.append g e cut)
      show (SImpl.run P mac ⟨w, sig⟩ (.append g e) cut).w = _ ∧ SigHonest P mac _ (SImpl.run P mac ⟨w, sig⟩ (.append g e) cut).sig
      rw [h1]
      exact ⟨hw, hmono⟩
  | recover g cut =>
    by_cases hg : g = w.m.gen
    · by_cases hm : w.m.mode = .opened
      · subst hg
        have hgate := honest_gate (mac := mac) L hI hs
        have h1 := simpl_recover (mac := mac) ⟨w, sig⟩ hm hgate cut
        have hw := impl_step_eq (P := P) w hb (.recover w.m.gen cut)
        have hws := step_recover_opened (P := P) w hm cut
        have hw0 := step_recover_opened (P := P) w hm none
        rcases hr : recoverPlan P ⟨w.m.gen, .reading⟩ w.fs.contents with ⟨m2, plan⟩
        rw [hr] at h1 hws hw0
        simp only at h1 hws hw0
        show (SImpl.run P mac ⟨w, sig⟩ (.recover w.m.gen) cut).w = _ ∧
          SigHonest P mac _ (SImpl.run P mac ⟨w, sig⟩ (.recover w.m.gen) cut).sig
        rw [h1]
        refine ⟨hw, ?_⟩
        by_cases hbz : m2.mode.isBusy
        · have hack : (step P m2 (.acked m2.gen)).1 = ack P m2 := by simp [ack, hbz]
          obtain ⟨hrd, hgk⟩ := ack_busy (P := P) m2 hbz
          simp only [hbz, ite_true] at hws hw0
          have hI0 : Inv P (World.finish P w m2 plan none) := by
            rw [← hw0]; exact (inv_step L hI (.recover w.m.gen none)).1
          have hm0 : (World.finish P w m2 plan none).m.mode = (ack P m2).mode := by rw [finish_none, hack]
          cases hmd : (ack P m2).mode with
          | ready hh c =>
            rw [hmd] at hm0
            by_cases hc : c = 0
            · have hsig : signSig mac (ack P m2) sig = sig := by simp [signSig, hmd, hc]
              cases cut with
              | none => simp only [recSig, hsig]; exact hmono
              | some cc => simp only [recSig, hsig, ite_self]; exact hmono
            · have hsig : signSig mac (ack P m2) sig = some (Sig.make mac c hh).toBytes := by simp [signSig, hmd, hc]
              cases cut with
              | none =>
                simp only [recSig, hsig]
                rw [hws]
                exact honest_finish L w _ _ hI0 hm0 hc none (by simp)
              | some cc =>
                by_cases hin : cc.n < plan.length
                · simp only [recSig, hin, ite_true]; exact hmono
                · simp only [recSig, hin, ite_false, hsig]
                  rw [hws]
                  exact honest_finish L w _ _ hI0 hm0 hc (some cc) (by intro cc' hc'; cases hc'; exact Nat.not_lt.1 hin)
          | _ => rw [hmd] at hrd; simp [isReady] at hrd
        · have hack : ack P m2 = m2 := ack_notBusy m2 hbz
          obtain ⟨_, hbk⟩ := recoverPlan_notBusy (P := P) ⟨w.m.gen, .reading⟩ w.fs.contents (by rw [hr]; exact hbz)
          rw [hr] at hbk
          simp only at hbk
          have hsig : signSig mac (ack P m2) sig = sig := by simp [signSig, hack, hbk]
          cases cut with
          | none => simp only [recSig, hsig]; exact hmono
          | some cc => simp only [recSig, hsig, ite_self]; exact hmono
      · have hr := step_recover_refused (P := P) w.m g (Or.inr hm)
        have h1 := simpl_refused (mac := mac) ⟨w, sig⟩ (.recover g) hb hr cut
        have hw := impl_step_eq (P := P) w hb (.recover g cut)
        show (SImpl.run P mac ⟨w, sig⟩ (.recover g) cut).w = _ ∧ SigHonest P mac _ (SImpl.run P mac ⟨w, sig⟩ (.recover g) cut).sig
        rw [h1]
        exact ⟨hw, hmono⟩
    · have hr := step_recover_refused (P := P) w.m g (Or.inl hg)
      have h1 := simpl_refused (mac := mac) ⟨w, sig⟩ (.recover g) hb hr cut
      have hw := impl_step_eq (P := P) w hb (.recover g cut)
      show (SImpl.run P mac ⟨w, sig⟩ (.recover g) cut).w = _ ∧ SigHonest P mac _ (SImpl.run P mac ⟨w, sig⟩ (.recover g) cut).sig
      rw [h1]
      exact ⟨hw, hmono⟩

/-- A list of events of the signed system. -/
def SImpl.runAll (P : Params) (mac : Nat → Digest → Bytes) (sw : SWorld) (evs : List WEvent) : SWorld := evs.foldl (SImpl.step P mac) sw

/-- **The signed driver is the model, and its signature is honest, whatever happens.** From the start (no journal, no signature), any events with any
crash points: the journal is what the slice 1 model gives (so every theorem of slice 1 holds of the signed driver), and the signature file is the
signature of a prefix of the journal (or none). -/
theorem signed_reachable (evs : List WEvent) :
    (SImpl.runAll P mac ⟨World.init, none⟩ evs).w = World.run P World.init evs ∧
    SigHonest P mac (World.run P World.init evs) (SImpl.runAll P mac ⟨World.init, none⟩ evs).sig := by
  have key : ∀ (evs : List WEvent) (sw : SWorld), Inv P sw.w → SigHonest P mac sw.w sw.sig →
      (SImpl.runAll P mac sw evs).w = World.run P sw.w evs ∧
      SigHonest P mac (World.run P sw.w evs) (SImpl.runAll P mac sw evs).sig := by
    intro evs
    induction evs with
    | nil => intro sw _ hs; exact ⟨rfl, hs⟩
    | cons ev evs ih =>
      intro sw hI hs
      obtain ⟨h1, h2⟩ := signed_step L hI hs ev
      have hI' := (inv_step L hI ev).1
      simp only [SImpl.runAll, World.run, List.foldl_cons] at ih ⊢
      have := ih (SImpl.step P mac sw ev) (by rw [h1]; exact hI') (by rw [h1]; exact h2)
      rw [h1] at this
      exact this
  exact key evs ⟨World.init, none⟩ inv_init (Or.inl rfl)

/-- **The verifier accepts the journal of the signed driver, whatever happened** (an unsigned tail is accepted, as lung does). -/
theorem signed_reachable_verifies (evs : List WEvent) :
    ∃ r v, read P (World.run P World.init evs).fs.contents = some r ∧
      verdict P mac r.entries (SImpl.runAll P mac ⟨World.init, none⟩ evs).sig = .ok v := by
  have hI := reachable_inv L (P := P) evs
  have hh := (signed_reachable (mac := mac) L evs).2
  have hg := honest_gate (mac := mac) L hI hh
  obtain ⟨r, hr⟩ := hI.readable
  unfold gateMsg at hg
  rw [hr] at hg
  simp only at hg
  cases hv : verdict P mac r.entries (SImpl.runAll P mac ⟨World.init, none⟩ evs).sig with
  | error e => rw [hv] at hg; simp at hg
  | ok v => exact ⟨r, v, hr, hv⟩

end Lawful

end VbmJournal
