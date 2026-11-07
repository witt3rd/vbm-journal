import VbmJournalProofs.Transfer
import VbmJournalProofs.Sig
/-! # The signed driver over the models of the shims

`driveSigned` is the driver with the signature: after every change the writer signs its head (`putSig`), and recovery checks the journal against the
signature before it writes anything (`sigGate`). Here is what it does over the models (`VbmJournal.Sim`), and that it makes what the verifier accepts.

**Plain statements.**

* `signed_append_ok`: an append that completes leaves the signature file holding the signature of the new head after the new count, and the
  journal file exactly as the unsigned driver leaves it (`signed_append_verifies`: and the verifier accepts that journal against that file, with no
  unsigned tail).
* `signed_append_fault`: an append that fails (a crash at an effect) leaves the signature file as it was, the journal as the unsigned driver leaves it.
  The old signature then covers a prefix of the journal that is left (`verdict_honest`): an unsigned tail, accepted.
* `signed_recover_refused`: **recovery refuses a journal whose signature fails** (cut back, rewritten, wrong key, unreadable): the writer is idle, and
  no byte of either file is written.
* `signed_recover_ok`: recovery of a journal whose signature holds does what the unsigned driver does, and signs the head it leaves
  (`signed_recover_verifies`: and the verifier accepts the recovered journal, with no unsigned tail). -/
set_option linter.unusedSectionVars false

namespace VbmJournal

variable {P : Params} {mac : Nat → Digest → Bytes}

@[simp] theorem sim_throw {α : Type} (e : String) (s : Sim) : (throw e : SimM α) s = (Except.error e, s) := rfl

/-- The signature file after `signHead` on the state `st`. -/
def signSig (mac : Nat → Digest → Bytes) (st : St) (sig : Option Bytes) : Option Bytes :=
  match st.mode with
  | .ready h c => if c = 0 then sig else some (Sig.make mac c h).toBytes
  | _ => sig

theorem signHead_sim (mac : Nat → Digest → Bytes) (st : St) (s : Sim) :
    signHead mac Shims.sim st s = (Except.ok (), { s with sig := signSig mac st s.sig }) := by
  obtain ⟨gen, mode⟩ := st
  cases mode <;> simp [signHead, signSig, Shims.sim]
  rename_i h c
  by_cases hc : c = 0 <;> simp [hc]

/-- The message of the signature gate, if it refuses. -/
def gateMsg (P : Params) (mac : Nat → Digest → Bytes) (sig : Option Bytes) (bytes : Bytes) : Option String :=
  match read P bytes with
  | none => none
  | some r => match verdict P mac r.entries sig with
    | .error e => some e
    | .ok _ => none

theorem sigGate_sim (bytes : Bytes) (s : Sim) :
    sigGate P mac Shims.sim bytes s = match gateMsg P mac s.sig bytes with
      | none => (Except.ok (), s)
      | some e => (Except.error e, s) := by
  unfold sigGate gateMsg
  cases hr : read P bytes with
  | none => rfl
  | some r =>
    simp only
    cases hv : verdict P mac r.entries s.sig <;> simp [Shims.sim, hv]

theorem driveSigned_eq (st : St) (ev : Event) (s : Sim) :
    driveSigned P mac Shims.sim st ev s = match driveRaw P Shims.sim (sigGate P mac Shims.sim) st ev s with
      | (Except.ok st', s') => (Except.ok (st', none), { s' with sig := if st' ≠ st then signSig mac st' s'.sig else s'.sig })
      | (Except.error e, s') => (Except.ok ((step P st .crash).1, some e), s') := by
  simp only [driveSigned, guarded, sim_tryCatch, sim_bind, sim_pure]
  rcases driveRaw P Shims.sim (sigGate P mac Shims.sim) st ev s with ⟨r, s'⟩
  cases r with
  | error e => rfl
  | ok st' =>
    by_cases hne : st' ≠ st <;> simp [hne, signHead_sim]

/-- An event whose plan does not read, signed. -/
theorem driveSigned_planned (st ev : _) (st1 : St) (plan : List Effect) (hst : step P st ev = (st1, plan)) (hno : NoRead plan)
    (fs : Fs) (sig : Option Bytes) (cut : Option Cut) :
    driveSigned P mac Shims.sim st ev ⟨fs, sig, cut, 0⟩ =
      match cut with
      | none => (Except.ok (ack P st1, none), ⟨fs.runAll plan, if ack P st1 ≠ st then signSig mac (ack P st1) sig else sig, none, plan.length⟩)
      | some c =>
        if c.n < plan.length then
          (Except.ok ((step P st .crash).1, some "cut"), ⟨(fs.runPrefix c.n plan).crash c.keep c.vanish, sig, some c, c.n⟩)
        else
          (Except.ok (ack P st1, none), ⟨fs.runAll plan, if ack P st1 ≠ st then signSig mac (ack P st1) sig else sig, some c, plan.length⟩) := by
  rw [driveSigned_eq]
  cases cut with
  | none =>
    simp [driveRaw, hst, runPlan_nocut plan hno ⟨fs, sig, none, 0⟩ rfl]
  | some c =>
    have h := runPlan_cut c plan hno ⟨fs, sig, some c, 0⟩ rfl
    by_cases hin : c.n < plan.length
    · simp [driveRaw, hst, h, hin]
    · simp [driveRaw, hst, h, hin]

/-- Signed recovery of a writer that has just taken over. -/
theorem driveSigned_recover (st : St) (hm : st.mode = .opened) (fs : Fs) (sig : Option Bytes) (cut : Option Cut) :
    match recoverPlan P ⟨st.gen, .reading⟩ fs.contents with
    | (m2, plan) =>
      driveSigned P mac Shims.sim st (.recover st.gen) ⟨fs, sig, cut, 0⟩ =
        match gateMsg P mac sig fs.contents with
        | some e => (Except.ok ((step P st .crash).1, some e), ⟨fs, sig, cut, 0⟩)
        | none =>
          match cut with
          | none => (Except.ok (ack P m2, none), ⟨fs.runAll plan, signSig mac (ack P m2) sig, none, plan.length⟩)
          | some c =>
            if c.n < plan.length then
              (Except.ok ((step P st .crash).1, some "cut"), ⟨(fs.runPrefix c.n plan).crash c.keep c.vanish, sig, some c, c.n⟩)
            else (Except.ok (ack P m2, none), ⟨fs.runAll plan, signSig mac (ack P m2) sig, some c, plan.length⟩) := by
  obtain ⟨gen, mode⟩ := st
  simp only at hm
  subst hm
  rcases hr : recoverPlan P ⟨gen, .reading⟩ fs.contents with ⟨m2, plan⟩
  have hno : NoRead plan := by have := recoverPlan_noRead (P := P) ⟨gen, .reading⟩ fs.contents; rw [hr] at this; exact this
  simp only
  rw [driveSigned_eq]
  rcases hg : gateMsg P mac sig fs.contents with _ | e
  · simp only
    have hne : ack P m2 ≠ (⟨gen, .opened⟩ : St) := by
      by_cases hbz : m2.mode.isBusy
      · intro heq
        have := (ack_busy (P := P) m2 hbz).1
        rw [heq] at this
        simp [isReady] at this
      · obtain ⟨_, hbk⟩ := recoverPlan_notBusy (P := P) ⟨gen, .reading⟩ fs.contents (by rw [hr]; exact hbz)
        rw [hr] at hbk
        simp only at hbk
        intro heq
        rw [ack_notBusy m2 hbz] at heq
        rw [heq] at hbk
        simp at hbk
    cases cut with
    | none =>
      simp [driveRaw, step, runPlan_readAll, sigGate_sim, hg, hr, runPlan_nocut plan hno ⟨fs, sig, none, 0⟩ rfl, hne]
    | some c =>
      have h := runPlan_cut c plan hno ⟨fs, sig, some c, 0⟩ rfl
      by_cases hin : c.n < plan.length
      · simp [driveRaw, step, runPlan_readAll, sigGate_sim, hg, hr, h, hin]
      · simp [driveRaw, step, runPlan_readAll, sigGate_sim, hg, hr, h, hin, hne]
  · simp [driveRaw, step, runPlan_readAll, sigGate_sim, hg]

/-! ## An append that completes -/

theorem signed_append_ok (st : St) {h : Digest} {c : Nat} (hm : st.mode = .ready h c) (e : Entry) (fs : Fs) (sig : Option Bytes) :
    driveSigned P mac Shims.sim st (.append st.gen e) ⟨fs, sig, none, 0⟩ =
      (Except.ok (⟨st.gen, .ready (P.link h (P.enc e)) (c + 1)⟩, none),
        ⟨fs.runAll (commitPlan none (encodeFrom P h [e]) (c == 0)), some (Sig.make mac (c + 1) (P.link h (P.enc e))).toBytes, none,
          (commitPlan none (encodeFrom P h [e]) (c == 0)).length⟩) := by
  have hst : step P st (.append st.gen e) =
      (⟨st.gen, .busy (P.link h (P.enc e)) (c + 1)⟩, commitPlan none (encodeFrom P h [e]) (c == 0)) := by
    simp [step, hm]
  rw [driveSigned_planned _ _ _ _ hst (commitPlan_noRead _ _ _)]
  have hack : ack P (⟨st.gen, .busy (P.link h (P.enc e)) (c + 1)⟩ : St) = ⟨st.gen, .ready (P.link h (P.enc e)) (c + 1)⟩ := by
    simp [ack, Mode.isBusy, step]
  have hne : (⟨st.gen, .ready (P.link h (P.enc e)) (c + 1)⟩ : St) ≠ st := fun heq => by
    have := congrArg (fun m : St => m.mode) heq
    simp [hm] at this
  simp [hack, hne, signSig]

/-- **The signature a completed append makes is accepted by the verifier**, with no unsigned tail: the journal is the old entries and the new one,
and the signature file holds the signature of its head after its count. -/
theorem signed_append_verifies (L : P.Lawful) {w : World} (hI : Inv P w) {h : Digest} {c : Nat} (hm : w.m.mode = .ready h c) (e : Entry) :
    ∃ r, read P (w.fs.runAll (commitPlan none (encodeFrom P h [e]) (c == 0))).contents = some r ∧
      r.entries = entriesOf P w.fs.contents ++ [e] ∧
      verdict P mac r.entries (some (Sig.make mac (c + 1) (P.link h (P.enc e))).toBytes) = .ok (.signed (c + 1) 0) := by
  have hstep : World.step P w (.append w.m.gen e none) =
      ⟨⟨w.m.gen, .ready (P.link h (P.enc e)) (c + 1)⟩, w.fs.runAll (commitPlan none (encodeFrom P h [e]) (c == 0))⟩ := by
    rw [step_append_ready w hm, finish_none, acked_busy]
  have hI' := (inv_step L hI (.append w.m.gen e none)).1
  rw [hstep] at hI'
  obtain ⟨r, hr, htail, hhead, hlen, _⟩ := hI'.rest
  refine ⟨r, hr, ?_, ?_⟩
  · obtain ⟨r0, hr0, htail0, hlen0, hdir, hdur, hh⟩ := ready_facts L hI hm
    have hent0 : entriesOf P w.fs.contents = r0.entries := by simp [entriesOf, hr0]
    have hc := commit_all w.fs hI.pending none (encodeFrom P h [e]) (c == 0)
    have hcont : (w.fs.runAll (commitPlan none (encodeFrom P h [e]) (c == 0))).contents = encodeFrom P P.genesis (r0.entries ++ [e]) := by
      rw [hc]
      simp only [Fs.contents, cutBase, List.append_nil, hdur]
      rw [encodeFrom_append, ← hh]
    have hr' := read_encode L (r0.entries ++ [e]) [] (by simp)
    rw [hcont] at hr
    simp only [List.append_nil] at hr'
    rw [hr'] at hr
    cases hr
    simp [hent0]
  · have hhd := (read_inv L _ _ hr).2.2
    have hl : r.entries.take (c + 1) = r.entries := List.take_of_length_le (by omega)
    have hsp : sp ∉ headFrom P P.genesis (r.entries.take (c + 1)) := by
      rw [hl, ← hhd, hhead]; exact (L.link_clean _ _).2
    have := verdict_honest (P := P) (mac := mac) (es := r.entries) (i := c + 1) (by omega) hsp
    rw [hl, ← hhd, hhead] at this
    rw [this]; simp [hlen]

/-! ## An append that fails -/

/-- **An append that fails** (the fault is at an effect of its plan) leaves the signature file as it was, and the journal file as the unsigned driver
leaves it: what a crash at that point leaves. The writer is idle. -/
theorem signed_append_fault (st : St) {h : Digest} {c : Nat} (hm : st.mode = .ready h c) (e : Entry) (fs : Fs) (sig : Option Bytes) (cc : Cut)
    (hn : cc.n < (commitPlan none (encodeFrom P h [e]) (c == 0)).length) :
    driveSigned P mac Shims.sim st (.append st.gen e) ⟨fs, sig, some cc, 0⟩ =
      (Except.ok ((step P st .crash).1, some "cut"),
        ⟨(fs.runPrefix cc.n (commitPlan none (encodeFrom P h [e]) (c == 0))).crash cc.keep cc.vanish, sig, some cc, cc.n⟩) := by
  have hst : step P st (.append st.gen e) =
      (⟨st.gen, .busy (P.link h (P.enc e)) (c + 1)⟩, commitPlan none (encodeFrom P h [e]) (c == 0)) := by
    simp [step, hm]
  rw [driveSigned_planned _ _ _ _ hst (commitPlan_noRead _ _ _)]
  simp [hn]

/-! ## Recovery -/

/-- **Recovery refuses a journal whose signature fails**: the signature file is unreadable, its mac is not the key's, the journal was cut back below
the signed point, or its chain at the signed point is not the signed head. The writer is idle, and no byte of either file is written. -/
theorem signed_recover_refused (st : St) (hm : st.mode = .opened) (fs : Fs) (sig : Option Bytes) (cut : Option Cut) (e : String)
    (hg : gateMsg P mac sig fs.contents = some e) :
    driveSigned P mac Shims.sim st (.recover st.gen) ⟨fs, sig, cut, 0⟩ =
      (Except.ok ((step P st .crash).1, some e), ⟨fs, sig, cut, 0⟩) := by
  have := driveSigned_recover (P := P) (mac := mac) st hm fs sig cut
  rcases hr : recoverPlan P ⟨st.gen, .reading⟩ fs.contents with ⟨m2, plan⟩
  rw [hr] at this
  simp only [hg] at this
  exact this

/-- The signature gate refuses exactly the journals the verifier refuses. -/
theorem gateMsg_of_verdict {bytes : Bytes} {r : Read} (hr : read P bytes = some r) {sig : Option Bytes} {e : String}
    (hv : verdict P mac r.entries sig = .error e) : gateMsg P mac sig bytes = some e := by
  simp [gateMsg, hr, hv]

/-- **Recovery of a journal whose signature holds** does what the unsigned driver does (`drive_recover`: the same machine state, the same file), and
signs the head it leaves. -/
theorem signed_recover_ok (st : St) (hm : st.mode = .opened) (fs : Fs) (sig : Option Bytes) (hg : gateMsg P mac sig fs.contents = none) :
    match recoverPlan P ⟨st.gen, .reading⟩ fs.contents with
    | (m2, plan) =>
      driveSigned P mac Shims.sim st (.recover st.gen) ⟨fs, sig, none, 0⟩ =
        (Except.ok (ack P m2, none), ⟨fs.runAll plan, signSig mac (ack P m2) sig, none, plan.length⟩) := by
  have := driveSigned_recover (P := P) (mac := mac) st hm fs sig none
  rcases hr : recoverPlan P ⟨st.gen, .reading⟩ fs.contents with ⟨m2, plan⟩
  rw [hr] at this
  simp only [hg] at this
  exact this

/-- **Recovery signs what it leaves, and the verifier accepts it**: a journal that verifies and whose signature holds is recovered, and the signature
file then holds the head after its count (a journal of no records is not signed), with no unsigned tail. -/
theorem signed_recover_verifies (L : P.Lawful) {w : World} (hI : Inv P w) (hm : w.m.mode = .opened) (sig : Option Bytes)
    (hg : gateMsg P mac sig w.fs.contents = none) :
    ∃ st' s', driveSigned P mac Shims.sim w.m (.recover w.m.gen) ⟨w.fs, sig, none, 0⟩ = (Except.ok (st', none), s') ∧
      ∃ h c, st'.mode = .ready h c ∧
        (c = 0 ∨ ∃ r, read P s'.fs.contents = some r ∧ s'.sig = some (Sig.make mac c h).toBytes ∧
          verdict P mac r.entries s'.sig = .ok (.signed c 0)) := by
  have hok := signed_recover_ok (P := P) (mac := mac) w.m hm w.fs sig hg
  have hw := step_recover_opened (P := P) w hm none
  rcases hr : recoverPlan P ⟨w.m.gen, .reading⟩ w.fs.contents with ⟨m2, plan⟩
  rw [hr] at hok hw
  simp only at hok hw
  have hI' := (inv_step L hI (.recover w.m.gen none)).1
  rw [hw] at hI'
  by_cases hbz : m2.mode.isBusy
  · simp only [hbz, ite_true, finish_none] at hI' hw
    have hack : (step P m2 (.acked m2.gen)).1 = ack P m2 := by simp [ack, hbz]
    rw [hack] at hI' hw
    obtain ⟨hrd, hgk⟩ := ack_busy (P := P) m2 hbz
    cases hmd : (ack P m2).mode with
    | ready h c =>
      refine ⟨ack P m2, _, hok, h, c, hmd, ?_⟩
      by_cases hc : c = 0
      · exact Or.inl hc
      · right
        have hrest := hI'.rest
        simp only [hmd, Mode.Rest] at hrest
        obtain ⟨r, hr', htail, hhead, hlen, _⟩ := hrest
        refine ⟨r, hr', by simp [signSig, hmd, hc], ?_⟩
        have hhd := (read_inv L _ _ hr').2.2
        have hl : r.entries.take c = r.entries := List.take_of_length_le (by omega)
        have hsp : sp ∉ headFrom P P.genesis (r.entries.take c) := by
          rw [hl]
          exact headFrom_clean L (by intro h0; rw [h0] at hlen; simp at hlen; omega)
        have := verdict_honest (P := P) (mac := mac) (es := r.entries) (i := c) (by omega) hsp
        rw [hl, ← hhd, hhead] at this
        simp only [signSig, hmd, hc, ite_false]
        rw [this]; simp [hlen]
    | _ => simp [hmd, isReady] at hrd
  · obtain ⟨_, hbk⟩ := recoverPlan_notBusy (P := P) ⟨w.m.gen, .reading⟩ w.fs.contents (by rw [hr]; exact hbz)
    rw [hr] at hbk
    simp only [hbz, Bool.false_eq_true, ite_false] at hI'
    simp only at hbk
    have := hI'.rest
    simp only [hbk, Mode.Rest] at this

end VbmJournal
