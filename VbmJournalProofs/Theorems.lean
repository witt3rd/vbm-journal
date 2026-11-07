import VbmJournalProofs.Recovery
/-! # The theorems of slice 1

**Plain statements.** `P` is any `Params` with `P.Lawful` (the digest binds, the codec round-trips). A *world* `w` satisfies `Inv`
(true of `World.init` and kept by every event: `reachable_inv`). `records w` is the journal: the entries of the file, once its
directory entry is durable.

(a) **Append-only.** `append_only`: after any list of events, with a crash at any point of any of them, every earlier state's
journal is a prefix of every later state's. `append_only_reachable` says it of the states reachable from `World.init`.

(b) **Chain integrity.** In `VbmJournalProofs.Chain`: a journal made only by appends verifies (`read_encode`); the head binds the
journal (`head_binds`, `headFrom_inj`); records reordered, duplicated or deleted from the middle fail (`verify_only_prefix`,
`perm_verifies_only_if_same`); an edited body fails (`edit_fails`); a cut or an edit before an anchor fails the anchor
(`anchored_unique`, `anchored_short_fails`). Here: the journal of every reachable state verifies (`reachable_verifies`).

(c) **Crash consistency.** `crash_consistency`: a crash at any point of an append (any number of effects done, any prefix of the
write kept, the file gone if its directory entry was not durable) leaves the journal as it was before the append or as it is after
it, never in between: `before` or `before ++ [e]`. `crash_before_effects`: if no effect ran it is `before`;
`crash_after_plan`: if the whole plan ran it is `after`. `recovered_after_crash`: and the journal that recovery then produces is
that, followed by the settlement of its calls in flight.

(d) **Fencing.** `stale_refused`: an event of a writer whose generation is not the current one changes nothing and plans nothing.
`takeOver_fences`: a take-over makes the generation one larger, so every older writer is stale. `world_takeOver_fences`: at the
level of the system, no append or recovery of an older generation does anything after a take-over. `accepted_is_live`: an event the
machine accepts is the live writer's, so at most one writer (`live_unique`) ever writes.

(e) **Recovery.** `reopen_settles`: reopening settles every call in flight as interrupted, once (`settle_once`), and closes them all
(`settle_closes`). `reopen_idempotent`: reopening a reopened journal changes nothing. `reopen_crash_safe`: a crash in the middle of
recovery, at any point, followed by recovery, gives the file a recovery that was not cut would have given. -/
set_option linter.unusedSectionVars false

namespace VbmJournal

variable {P : Params} {w : World}

/-! ## (a) Append-only -/

section Lawful
variable (L : P.Lawful)
include L

/-- **(a) Append-only.** Any events, with any crash points: the invariant holds after, and the journal only grows. -/
theorem append_only (evs : List WEvent) : ∀ (w : World), Inv P w →
    Inv P (w.run P evs) ∧ World.records P w <+: World.records P (w.run P evs) := by
  induction evs with
  | nil => intro w hI; exact ⟨hI, List.prefix_refl _⟩
  | cons ev evs ih =>
    intro w hI
    obtain ⟨h1, h2⟩ := inv_step L hI ev
    obtain ⟨h3, h4⟩ := ih _ h1
    exact ⟨h3, h2.trans h4⟩

theorem reachable_inv (evs : List WEvent) : Inv P (World.init.run P evs) :=
  (append_only L evs World.init inv_init).1

/-- **(a) for the reachable states**: the journal after the events `evs₁` is a prefix of the journal after `evs₁ ++ evs₂`. -/
theorem append_only_reachable (evs₁ evs₂ : List WEvent) :
    World.records P (World.init.run P evs₁) <+: World.records P (World.init.run P (evs₁ ++ evs₂)) := by
  have := (append_only L evs₂ _ (reachable_inv L evs₁)).2
  simpa [World.run, List.foldl_append] using this

/-- **(b)** The file of every reachable state verifies: the journal is a chain from the genesis digest (a torn tail aside). -/
theorem reachable_verifies (evs : List WEvent) : ∃ r, read P (World.init.run P evs).fs.contents = some r :=
  (reachable_inv L evs).readable

/-! ## (c) Crash consistency -/

theorem ready_facts (hI : Inv P w) {h : Digest} {c : Nat} (hm : w.m.mode = .ready h c) :
    ∃ r, read P w.fs.contents = some r ∧ r.tail = [] ∧ r.entries.length = c ∧ (w.fs.dirSafe = true ∨ c = 0) ∧
      w.fs.durable = encodeFrom P P.genesis r.entries ++ [] ∧ h = headFrom P P.genesis r.entries := by
  have hrest := hI.rest
  rw [hm] at hrest
  obtain ⟨r, hrd, htail, hhead, hlen, hdir⟩ := hrest
  obtain ⟨hd, hnl, hh⟩ := read_inv L _ r hrd
  refine ⟨r, hrd, htail, hlen, hdir, ?_, hhead.symm.trans hh⟩
  rw [← htail, ← contents_of_pending_nil hI.pending]; exact hd

omit L in
theorem crash_cases (f : Fs) (hp : f.pending = []) (k : Nat) (v : Bool) :
    f.crash k v = f ∨ (f.crash k v = Fs.empty ∧ f.dirSafe = false) := by
  obtain ⟨d, p, s⟩ := f
  simp only at hp
  subst hp
  by_cases hv : (v && !s) = true
  · right
    refine ⟨by simp [Fs.crash, hv], ?_⟩
    cases s <;> simp_all
  · left; simp only [Fs.crash, hv]; simp

/-- **(c) Crash consistency.** A crash at any point of an append leaves the journal as it was, or as it is once the append is complete:
never anything in between. -/
theorem crash_consistency (hI : Inv P w) {h : Digest} {c : Nat} (hm : w.m.mode = .ready h c) (e : Entry) (cc : Cut) :
    entriesOf P (w.step P (.append w.m.gen e (some cc))).fs.contents = entriesOf P w.fs.contents ∨
    entriesOf P (w.step P (.append w.m.gen e (some cc))).fs.contents = entriesOf P w.fs.contents ++ [e] := by
  obtain ⟨r, hrd, htail, hlen, hdir, hdur, hh⟩ := ready_facts L hI hm
  have hent : entriesOf P w.fs.contents = r.entries := by simp [entriesOf, hrd]
  rw [step_append_ready w hm, finish_some, hent]
  subst hh
  obtain ⟨h1, h2, h3⟩ := cut_read (P := P) L w.fs hI.pending r.entries [e] [] (by simp) hdur none (fun _ => rfl) (by simp)
    (c == 0) cc.n cc.keep cc.vanish
  rcases h3 with ⟨j, r', hj, hr', he⟩ | ⟨h4, h5⟩
  · have : entriesOf P ((w.fs.runPrefix cc.n (commitPlan none (encodeFrom P (headFrom P P.genesis r.entries) [e]) (c == 0))).crash
        cc.keep cc.vanish).contents = r.entries ++ [e].take j := by
      simp [entriesOf, hr', he]
    rw [this]
    have hj1 : j = 0 ∨ j = 1 := by simp at hj; omega
    rcases hj1 with rfl | rfl
    · left; simp
    · right; simp
  · left
    have hc0 : c = 0 := by simp [h5] at hdir; exact hdir
    have hnil : r.entries = [] := List.eq_nil_of_length_eq_zero (by omega)
    unfold entriesOf
    rw [h4, read_empty]
    simp [hnil]

/-- **(c)** If the crash came before any effect ran, the journal is as it was. -/
theorem crash_before_effects (hI : Inv P w) {h : Digest} {c : Nat} (hm : w.m.mode = .ready h c) (e : Entry) (cc : Cut)
    (hn : cc.n = 0) :
    entriesOf P (w.step P (.append w.m.gen e (some cc))).fs.contents = entriesOf P w.fs.contents := by
  obtain ⟨r, hrd, htail, hlen, hdir, hdur, hh⟩ := ready_facts L hI hm
  have hent : entriesOf P w.fs.contents = r.entries := by simp [entriesOf, hrd]
  rw [step_append_ready w hm, finish_some, hent, hn]
  simp only [Fs.runPrefix, List.take_zero, List.foldl_nil]
  rcases crash_cases w.fs hI.pending cc.keep cc.vanish with h1 | ⟨h1, h2⟩
  · simp [h1, hent]
  · have hc0 : c = 0 := by simp [h2] at hdir; exact hdir
    have hnil : r.entries = [] := List.eq_nil_of_length_eq_zero (by omega)
    unfold entriesOf
    rw [h1]
    simp [hnil, Fs.contents, Fs.empty, read_empty]

/-- **(c)** If the whole plan had run, the journal is as it is once the append is complete. -/
theorem crash_after_plan (hI : Inv P w) {h : Digest} {c : Nat} (hm : w.m.mode = .ready h c) (e : Entry) (cc : Cut)
    (hn : (commitPlan none (encodeFrom P h [e]) (c == 0)).length ≤ cc.n) :
    entriesOf P (w.step P (.append w.m.gen e (some cc))).fs.contents = entriesOf P w.fs.contents ++ [e] := by
  obtain ⟨r, hrd, htail, hlen, hdir, hdur, hh⟩ := ready_facts L hI hm
  have hent : entriesOf P w.fs.contents = r.entries := by simp [entriesOf, hrd]
  rw [step_append_ready w hm, finish_some, hent]
  simp only [Fs.runPrefix, List.take_of_length_le hn]
  subst hh
  have hfull : w.fs.runAll (commitPlan none (encodeFrom P (headFrom P P.genesis r.entries) [e]) (c == 0)) =
      ⟨encodeFrom P P.genesis (r.entries ++ [e]), [], w.fs.dirSafe || (c == 0)⟩ :=
    full_run (P := P) w.fs hI.pending r.entries [e] [] hdur none (fun _ => rfl) (by simp) (c == 0)
  have hsafe : (w.fs.dirSafe || c == 0) = true := by rcases hdir with h1 | h1 <;> simp [h1]
  have hread := read_encode L (r.entries ++ [e]) [] (by simp)
  simp only [Fs.runAll] at hfull
  rw [hfull]
  have hread' : read P (encodeFrom P P.genesis (r.entries ++ [e])) =
      some ⟨r.entries ++ [e], headFrom P P.genesis (r.entries ++ [e]), []⟩ := by simpa using hread
  simp [Fs.crash, hsafe, entriesOf, Fs.contents, hread']


/-! ## (e) Recovery -/

omit L in
theorem fs_ext {f g : Fs} (hf : f.pending = []) (hg : g.pending = []) (hc : f.contents = g.contents)
    (hd : f.dirSafe = g.dirSafe) : f = g := by
  obtain ⟨d, p, s⟩ := f
  obtain ⟨d', p', s'⟩ := g
  simp only at hf hg hd
  subst hf hg hd
  simp only [Fs.contents, List.append_nil] at hc
  rw [hc]

theorem entriesOf_encode (es : List Entry) : entriesOf P (encodeFrom P P.genesis es) = es := by
  have := read_encode L es [] (by simp)
  simp only [List.append_nil] at this
  simp [entriesOf, this]

/-- Reopening, computed: the file becomes the verified entries followed by their settlement. -/
theorem reopen_spec (hI : Inv P w) : ∃ r, read P w.fs.contents = some r ∧
    (w.reopen P).fs.pending = [] ∧
    (w.reopen P).fs.contents = encodeFrom P P.genesis (r.entries ++ settleEntries r.entries) ∧
    (w.reopen P).m.mode = .ready (headFrom P P.genesis (r.entries ++ settleEntries r.entries)) (r.entries ++ settleEntries r.entries).length ∧
    (w.fs.contents ≠ [] → (w.reopen P).fs.dirSafe = true) ∧
    (w.fs.contents = [] → (w.reopen P).fs = w.fs) ∧
    Inv P (w.reopen P) := by
  have hI1 := (inv_step_takeOver L hI).1
  have hm1 : (w.step P .takeOver).m.mode = .opened := by rw [step_takeOver]
  have hfs : (w.step P .takeOver).fs = w.fs := by rw [step_takeOver]
  obtain ⟨r, hr, hmm, hp, hc, hd, he⟩ := recover_spec L hI1 hm1
  rw [hfs] at hr hd he
  refine ⟨r, hr, hp, hc, by simp only [World.reopen]; rw [hmm], hd, he, ?_⟩
  have := (inv_step L hI1 (.recover (w.step P .takeOver).m.gen none)).1
  exact this

/-- **(e) Recovery settles every call in flight, exactly once.** -/
theorem reopen_settles (hI : Inv P w) : ∃ E, entriesOf P w.fs.contents = E ∧
    entriesOf P (w.reopen P).fs.contents = E ++ settleEntries E ∧
    openCalls (E ++ settleEntries E) = [] ∧
    ∀ id, doneCount id (E ++ settleEntries E) = doneCount id E + (if id ∈ openCalls E then 1 else 0) := by
  obtain ⟨r, hr, _, hc, _⟩ := reopen_spec L hI
  refine ⟨r.entries, by simp [entriesOf, hr], ?_, settle_closes _, settle_once _⟩
  rw [hc, entriesOf_encode L]

/-- **(e) Recovery is idempotent**: reopening a reopened journal changes nothing (the file, the writer's head and count). -/
theorem reopen_idempotent (hI : Inv P w) :
    ((w.reopen P).reopen P).fs = (w.reopen P).fs ∧ ((w.reopen P).reopen P).m.mode = (w.reopen P).m.mode := by
  obtain ⟨r, hr, hp, hc, hmode, hd, he, hI1⟩ := reopen_spec L hI
  obtain ⟨r1, hr1, hp1, hc1, hmode1, hd1, he1, _⟩ := reopen_spec L hI1
  have hread := read_encode L (r.entries ++ settleEntries r.entries) [] (by simp)
  rw [hc] at hr1
  have hr1' : read P (encodeFrom P P.genesis (r.entries ++ settleEntries r.entries)) =
      some ⟨r.entries ++ settleEntries r.entries, headFrom P P.genesis (r.entries ++ settleEntries r.entries), []⟩ := by
    simpa using hread
  rw [hr1'] at hr1
  have hr1e := Option.some.inj hr1
  have hent : r1.entries = r.entries ++ settleEntries r.entries := by rw [← hr1e]
  have hidem : r1.entries ++ settleEntries r1.entries = r.entries ++ settleEntries r.entries := by
    rw [hent, settle_idem]; simp
  refine ⟨?_, ?_⟩
  · by_cases hE : (w.reopen P).fs.contents = []
    · exact he1 hE
    · refine fs_ext hp1 hp ?_ ?_
      · rw [hc1, hc, hidem]
      · rw [hd1 hE]
        by_cases hE0 : w.fs.contents = []
        · exfalso; apply hE; rw [he hE0]; exact hE0
        · exact (hd hE0).symm
  · rw [hmode1, hmode, hidem]

/-- **(e) A crash in the middle of recovery, at any point, then recovery**, leaves the file a recovery that was not cut would have left
(when the journal's directory entry is durable, as it is once anything in it was acknowledged or any recovery completed). -/
theorem reopen_crash_safe (hI : Inv P w) (hs : w.fs.dirSafe = true) (cc : Cut) :
    ((w.reopenCut P cc).reopen P).fs.contents = (w.reopen P).fs.contents := by
  have hI1 := (inv_step_takeOver L hI).1
  have hm1 : (w.step P .takeOver).m.mode = .opened := by rw [step_takeOver]
  have hfs : (w.step P .takeOver).fs = w.fs := by rw [step_takeOver]
  have hs1 : (w.step P .takeOver).fs.dirSafe = true := by rw [hfs]; exact hs
  obtain ⟨r, j, hr, hj, hent, hsafe⟩ := recover_cut_spec L hI1 hm1 hs1 cc
  rw [hfs] at hr
  have hI2 : Inv P (w.reopenCut P cc) := (inv_step L hI1 (.recover (w.step P .takeOver).m.gen (some cc))).1
  obtain ⟨r2, hr2, _, hc2, _⟩ := reopen_spec L hI2
  obtain ⟨r0, hr0, _, hc0, _⟩ := reopen_spec L hI
  rw [hr0] at hr
  have hrr : r0 = r := (Option.some.inj hr)
  subst hrr
  have e2 : r2.entries = r0.entries ++ (settleEntries r0.entries).take j := by
    have : entriesOf P (w.reopenCut P cc).fs.contents = r0.entries ++ (settleEntries r0.entries).take j := hent
    rw [← this]; simp [entriesOf, hr2]
  rw [hc2, hc0, e2, settle_partial]
  congr 1
  rw [List.append_assoc, List.take_append_drop]

/-- **(c)** After a crash in an append, recovery produces the journal before the append or after it, followed by the settlement of
the calls that journal has in flight. -/
theorem recovered_after_crash (hI : Inv P w) {h : Digest} {c : Nat} (hm : w.m.mode = .ready h c) (e : Entry) (cc : Cut) :
    ∃ E, (E = entriesOf P w.fs.contents ∨ E = entriesOf P w.fs.contents ++ [e]) ∧
      entriesOf P ((w.step P (.append w.m.gen e (some cc))).reopen P).fs.contents = E ++ settleEntries E := by
  have hI' := (inv_step L hI (.append w.m.gen e (some cc))).1
  obtain ⟨r, hr, _, hc, _⟩ := reopen_spec L hI'
  refine ⟨r.entries, ?_, ?_⟩
  · have hcc := crash_consistency L hI hm e cc
    have hE : entriesOf P (w.step P (.append w.m.gen e (some cc))).fs.contents = r.entries := by simp [entriesOf, hr]
    rw [hE] at hcc
    exact hcc
  · rw [hc, entriesOf_encode L]

/-! ## (d) Fencing -/

omit L in
/-- **(d) Fencing.** An event of a writer whose generation is not the current one changes nothing and plans nothing. -/
theorem stale_refused (st : St) {g : Nat} (hg : g ≠ st.gen) (e : Entry) (b : Bytes) :
    step P st (.append g e) = (st, []) ∧ step P st (.recover g) = (st, []) ∧
    step P st (.readReply g b) = (st, []) ∧ step P st (.acked g) = (st, []) := by
  simp [step, hg]

omit L in
/-- **(d)** A take-over makes the generation one larger and the new writer the live one, so every older writer is stale. -/
theorem takeOver_fences (st : St) :
    (step P st .takeOver).1.gen = st.gen + 1 ∧ (step P st .takeOver).1.mode = .opened ∧
    ∀ g, g < (step P st .takeOver).1.gen → ∀ (e : Entry) (b : Bytes),
      step P (step P st .takeOver).1 (.append g e) = ((step P st .takeOver).1, []) ∧
      step P (step P st .takeOver).1 (.recover g) = ((step P st .takeOver).1, []) ∧
      step P (step P st .takeOver).1 (.readReply g b) = ((step P st .takeOver).1, []) ∧
      step P (step P st .takeOver).1 (.acked g) = ((step P st .takeOver).1, []) := by
  refine ⟨rfl, rfl, fun g hg e b => ?_⟩
  exact stale_refused _ (by simp [step] at hg ⊢; omega) e b

omit L in
/-- **(d)** At the level of the system: after a take-over, no append or recovery of an older generation does anything. -/
theorem world_takeOver_fences (w : World) {g : Nat} (hg : g ≤ w.m.gen) (e : Entry) (cut : Option Cut) :
    (w.step P .takeOver).step P (.append g e cut) = w.step P .takeOver ∧
    (w.step P .takeOver).step P (.recover g cut) = w.step P .takeOver := by
  have hne : g ≠ (w.step P .takeOver).m.gen := by rw [step_takeOver]; simp only; omega
  exact ⟨step_append_stale _ hne e cut, step_recover_stale _ hne cut⟩

/-- The live writer: the one of the current generation, when there is a writer at all. -/
def Live (st : St) (g : Nat) : Prop := g = st.gen ∧ st.mode ≠ .idle

/-- **(d) At most one live writer.** -/
theorem live_unique {st : St} {g g' : Nat} (h : Live st g) (h' : Live st g') : g = g' := h.1.trans h'.1.symm

omit L in
/-- **(d)** What the machine accepts is the live writer's: an append that plans anything, and a recovery or acknowledgement that changes
the state, come from the live writer of the current generation. -/
theorem accepted_is_live (st : St) (g : Nat) (e : Entry) :
    ((step P st (.append g e)).2 ≠ [] → Live st g) ∧
    (step P st (.recover g) ≠ (st, []) → Live st g) ∧
    (step P st (.acked g) ≠ (st, []) → Live st g) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro h <;> by_cases hg : g = st.gen <;> obtain ⟨gen, mode⟩ := st <;> simp only at hg <;>
    (try subst hg) <;> cases mode <;> simp_all [step, Live]

omit L in
/-- The generation never goes down: only a take-over raises it. -/
theorem gen_mono (st : St) (ev : Event) : st.gen ≤ (step P st ev).1.gen := by
  obtain ⟨gen, mode⟩ := st
  cases ev with
  | takeOver => simp [step]
  | crash => simp [step]
  | recover g => cases mode <;> by_cases hg : g = gen <;> simp [step, hg]
  | readReply g b =>
    cases mode <;> by_cases hg : g = gen <;> simp [step, hg]
    cases h : read P b <;> simp [recoverPlan, h]
    split <;> simp
  | append g e => cases mode <;> by_cases hg : g = gen <;> simp [step, hg]
  | acked g => cases mode <;> by_cases hg : g = gen <;> simp [step, hg]

end Lawful

end VbmJournal
