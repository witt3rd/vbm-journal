import VbmJournalProofs.Fs
/-! # The invariant of the world, and the one-step theorem

`Inv` holds of every state reachable from `World.init`; `inv_step` says one event of the system (any event, with any crash point)
keeps it, and never loses a record of the journal (append-only, theorem (a)). The theorems of crash consistency, fencing and
recovery (`VbmJournalProofs.Theorems`) are read off the step lemmas here. -/
set_option linter.unusedSectionVars false

namespace VbmJournal

variable {P : Params}

/-- The entries a reader finds in some bytes (none when the bytes fail verification). -/
def entriesOf (P : Params) (b : Bytes) : List Entry := ((read P b).map (·.entries)).getD []

/-- **The journal**: the entries of the file, once its directory entry is durable (before that the file may vanish in a crash, so
nothing in it is yet part of the journal). -/
def World.records (P : Params) (w : World) : List Entry :=
  if w.fs.dirSafe then entriesOf P w.fs.contents else []

/-- What a writer in this mode, between two events, knows of the file. A plan is never outstanding between events. -/
def Mode.Rest (P : Params) (fs : Fs) : Mode → Prop
  | .idle => True
  | .opened => True
  | .reading => False
  | .ready h c => ∃ r, read P fs.contents = some r ∧ r.tail = [] ∧ r.head = h ∧ r.entries.length = c ∧ (fs.dirSafe = true ∨ c = 0)
  | .busy _ _ => False
  | .broken => False

/-- The invariant: the file is a verifying journal (possibly with a torn tail), nothing is pending, and a ready writer's head and count
are the file's. -/
structure Inv (P : Params) (w : World) : Prop where
  pending : w.fs.pending = []
  readable : ∃ r, read P w.fs.contents = some r
  rest : Mode.Rest P w.fs w.m.mode

theorem read_empty : read P [] = some ⟨[], P.genesis, []⟩ := by
  simp [read, parseLines, verifyFrom]

theorem inv_init : Inv P World.init :=
  ⟨rfl, ⟨_, read_empty⟩, trivial⟩

/-! ## Unfolding the system step -/

theorem step_takeOver (w : World) : w.step P .takeOver = ⟨⟨w.m.gen + 1, .opened⟩, w.fs⟩ := by
  simp [World.step, VbmJournal.step]

theorem step_crash (w : World) (k : Nat) (v : Bool) : w.step P (.crash k v) = ⟨⟨w.m.gen, .idle⟩, w.fs.crash k v⟩ := by
  simp [World.step, VbmJournal.step]

theorem step_append_stale (w : World) {g : Nat} (hg : g ≠ w.m.gen) (e : Entry) (cut : Option Cut) :
    w.step P (.append g e cut) = w := by
  simp [World.step, VbmJournal.step, hg]

theorem step_append_ready (w : World) {h : Digest} {c : Nat} (hm : w.m.mode = .ready h c) (e : Entry) (cut : Option Cut) :
    w.step P (.append w.m.gen e cut) =
      w.finish P ⟨w.m.gen, .busy (P.link h (P.enc e)) (c + 1)⟩ (commitPlan none (encodeFrom P h [e]) (c == 0)) cut := by
  obtain ⟨⟨gen, mode⟩, fs⟩ := w
  simp only at hm
  subst hm
  simp [World.step, VbmJournal.step]

theorem step_append_other (w : World) (g : Nat) (e : Entry) (cut : Option Cut) (h : ∀ h c, w.m.mode ≠ .ready h c) :
    w.step P (.append g e cut) = w := by
  obtain ⟨⟨gen, mode⟩, fs⟩ := w
  cases mode with
  | ready hh c => exact absurd rfl (h hh c)
  | _ => simp [World.step, VbmJournal.step]

theorem step_recover_stale (w : World) {g : Nat} (hg : g ≠ w.m.gen) (cut : Option Cut) :
    w.step P (.recover g cut) = w := by
  simp [World.step, VbmJournal.step, hg]

theorem step_recover_other (w : World) (g : Nat) (cut : Option Cut) (h : w.m.mode ≠ .opened) :
    w.step P (.recover g cut) = w := by
  obtain ⟨⟨gen, mode⟩, fs⟩ := w
  cases mode with
  | opened => exact absurd rfl h
  | _ => simp [World.step, VbmJournal.step]

theorem step_recover_opened (w : World) (hm : w.m.mode = .opened) (cut : Option Cut) :
    w.step P (.recover w.m.gen cut) =
      match recoverPlan P ⟨w.m.gen, .reading⟩ w.fs.contents with
      | (m2, plan) => if m2.mode.isBusy then w.finish P m2 plan cut else ⟨m2, w.fs⟩ := by
  obtain ⟨⟨gen, mode⟩, fs⟩ := w
  simp only at hm
  subst hm
  simp [World.step, VbmJournal.step]


theorem finish_none (w : World) (m1 : St) (plan : List Effect) :
    w.finish P m1 plan none = ⟨(VbmJournal.step P m1 (.acked m1.gen)).1, w.fs.runAll plan⟩ := rfl

theorem finish_some (w : World) (m1 : St) (plan : List Effect) (c : Cut) :
    w.finish P m1 plan (some c) = ⟨(VbmJournal.step P m1 .crash).1, (w.fs.runPrefix c.n plan).crash c.keep c.vanish⟩ := rfl

theorem acked_busy (gen : Nat) (h : Digest) (c : Nat) :
    (VbmJournal.step P ⟨gen, .busy h c⟩ (.acked gen)).1 = ⟨gen, .ready h c⟩ := by
  simp [VbmJournal.step]

theorem crash_idle (m : St) : (VbmJournal.step P m .crash).1 = ⟨m.gen, .idle⟩ := rfl

/-- The records of two files, when the first is a prefix of the second. -/
theorem records_prefix {f f' : Fs} {E E' : List Entry}
    (h : f.dirSafe = true → f'.dirSafe = true ∧ E <+: E') :
    (if f.dirSafe then E else []) <+: (if f'.dirSafe then E' else []) := by
  cases hs : f.dirSafe
  · simp
  · obtain ⟨h1, h2⟩ := h hs
    simp [h1, h2]

section Lawful
variable (L : P.Lawful)
include L

omit L in
theorem cutBase_eq (f : Fs) (es : List Entry) (t : Bytes) (hd : f.durable = encodeFrom P P.genesis es ++ t)
    (cut : Option Nat) (hc0 : cut = none → t = []) (hc1 : ∀ n, cut = some n → n = (encodeFrom P P.genesis es).length) :
    cutBase cut f.durable = encodeFrom P P.genesis es := by
  cases cut with
  | none => simp [cutBase, hd, hc0 rfl]
  | some n => simp [cutBase, hd, hc1 n rfl]

/-- **A plan cut anywhere, then a crash**: the file reads back as the entries it had, then the first `j` entries of what was being
written (none, some, or all), then a torn tail; or, if its directory entry was never durable, it is gone. -/
theorem cut_read (f : Fs) (hp : f.pending = []) (es ss : List Entry) (t : Bytes) (ht : nl ∉ t)
    (hd : f.durable = encodeFrom P P.genesis es ++ t) (cut : Option Nat)
    (hc0 : cut = none → t = []) (hc1 : ∀ n, cut = some n → n = (encodeFrom P P.genesis es).length)
    (dir : Bool) (n keep : Nat) (vanish : Bool) :
    ((f.runPrefix n (commitPlan cut (encodeFrom P (headFrom P P.genesis es) ss) dir)).crash keep vanish).pending = [] ∧
    (f.dirSafe = true → ((f.runPrefix n (commitPlan cut (encodeFrom P (headFrom P P.genesis es) ss) dir)).crash keep vanish).dirSafe = true) ∧
    ((∃ j r, j ≤ ss.length ∧
        read P ((f.runPrefix n (commitPlan cut (encodeFrom P (headFrom P P.genesis es) ss) dir)).crash keep vanish).contents = some r ∧
        r.entries = es ++ ss.take j) ∨
     (((f.runPrefix n (commitPlan cut (encodeFrom P (headFrom P P.genesis es) ss) dir)).crash keep vanish).contents = [] ∧ f.dirSafe = false)) := by
  obtain ⟨hp1, hp2, k, hk, hcase⟩ := commit_cut f hp cut (encodeFrom P (headFrom P P.genesis es) ss) dir n keep vanish
  refine ⟨hp1, hp2, ?_⟩
  rw [contents_of_pending_nil hp1]
  have hb := cutBase_eq f es t hd cut hc0 hc1
  rcases hcase with h | h | ⟨h, hs⟩
  · left
    rw [h, hd]
    exact ⟨0, _, Nat.zero_le _, read_encode L es t ht, by simp⟩
  · left
    obtain ⟨j, t', hj, _, hr⟩ := read_partial L ss es k
    rw [h, hb]
    exact ⟨j, _, hj, hr, rfl⟩
  · exact Or.inr ⟨h, hs⟩

omit L in
theorem crash_fs (f : Fs) (hp : f.pending = []) (hr : ∃ r, read P f.contents = some r) (k : Nat) (v : Bool) :
    (f.crash k v).pending = [] ∧ (∃ r, read P (f.crash k v).contents = some r) ∧ (f.dirSafe = true → f.crash k v = f) := by
  obtain ⟨d, p, s⟩ := f
  simp only at hp
  subst hp
  by_cases hv : (v && !s) = true
  · simp only [Fs.crash, hv, ite_true]
    refine ⟨rfl, ⟨_, read_empty⟩, ?_⟩
    intro hs
    simp [hs] at hv
  · simp only [Fs.crash, hv]
    simp only [List.take_nil, List.append_nil]
    exact ⟨rfl, hr, fun _ => rfl⟩

omit L in
theorem full_run (f : Fs) (hp : f.pending = []) (es ss : List Entry) (t : Bytes)
    (hd : f.durable = encodeFrom P P.genesis es ++ t) (cut : Option Nat)
    (hc0 : cut = none → t = []) (hc1 : ∀ n, cut = some n → n = (encodeFrom P P.genesis es).length) (dir : Bool) :
    f.runAll (commitPlan cut (encodeFrom P (headFrom P P.genesis es) ss) dir) =
      ⟨encodeFrom P P.genesis (es ++ ss), [], f.dirSafe || dir⟩ := by
  rw [commit_all f hp, cutBase_eq f es t hd cut hc0 hc1, encodeFrom_append]

/-! ## One event keeps the invariant and never loses a record -/

variable {w : World}

theorem inv_step_takeOver (hI : Inv P w) :
    Inv P (w.step P .takeOver) ∧ World.records P w <+: World.records P (w.step P .takeOver) := by
  rw [step_takeOver]
  exact ⟨⟨hI.pending, hI.readable, trivial⟩, List.prefix_refl _⟩

theorem inv_step_crash (hI : Inv P w) (k : Nat) (v : Bool) :
    Inv P (w.step P (.crash k v)) ∧ World.records P w <+: World.records P (w.step P (.crash k v)) := by
  rw [step_crash]
  obtain ⟨h1, h2, h3⟩ := crash_fs w.fs hI.pending hI.readable k v
  refine ⟨⟨h1, h2, trivial⟩, ?_⟩
  unfold World.records
  refine records_prefix ?_
  intro hs
  rw [h3 hs]
  exact ⟨hs, List.prefix_refl _⟩

/-- The accepted append, as one lemma on the state before. -/
theorem inv_step_append_ready (hI : Inv P w) {h : Digest} {c : Nat} (hm : w.m.mode = .ready h c) (e : Entry) (cut : Option Cut) :
    Inv P (w.step P (.append w.m.gen e cut)) ∧ World.records P w <+: World.records P (w.step P (.append w.m.gen e cut)) := by
  rw [step_append_ready w hm]
  have hrest := hI.rest
  rw [hm] at hrest
  obtain ⟨r, hrd, htail, hhead, hlen, hdir⟩ := hrest
  obtain ⟨hd, hnl, hh⟩ := read_inv L _ r hrd
  rw [contents_of_pending_nil hI.pending, htail] at hd
  have hdur : w.fs.durable = encodeFrom P P.genesis r.entries ++ [] := hd
  have hent : entriesOf P w.fs.contents = r.entries := by simp [entriesOf, hrd]
  have hh' : h = headFrom P P.genesis r.entries := hhead.symm.trans hh
  subst hh'
  cases cut with
  | none =>
    rw [finish_none, acked_busy]
    have hfull : w.fs.runAll (commitPlan none (encodeFrom P (headFrom P P.genesis r.entries) [e]) (c == 0)) =
        ⟨encodeFrom P P.genesis (r.entries ++ [e]), [], w.fs.dirSafe || (c == 0)⟩ :=
      full_run (P := P) w.fs hI.pending r.entries [e] [] hdur none (fun _ => rfl) (by simp) (c == 0)
    have hsafe : (w.fs.dirSafe || c == 0) = true := by
      rcases hdir with h1 | h1 <;> simp [h1]
    have hread := read_encode L (r.entries ++ [e]) [] (by simp)
    rw [hfull]
    refine ⟨⟨rfl, ⟨_, by simpa [Fs.contents] using hread⟩, ?_⟩, ?_⟩
    · refine ⟨_, by simpa [Fs.contents] using hread, rfl, ?_, by simp [hlen], Or.inl hsafe⟩
      simp [headFrom_snoc]
    · unfold World.records
      refine records_prefix ?_
      intro _
      refine ⟨hsafe, ?_⟩
      rw [hent]
      have : entriesOf P (Fs.contents ⟨encodeFrom P P.genesis (r.entries ++ [e]), [], w.fs.dirSafe || (c == 0)⟩) =
          r.entries ++ [e] := by
        have hread' : read P (encodeFrom P P.genesis (r.entries ++ [e])) =
            some ⟨r.entries ++ [e], headFrom P P.genesis (r.entries ++ [e]), []⟩ := by simpa using hread
        simp [entriesOf, Fs.contents, hread']
      rw [this]
      exact List.prefix_append _ _
  | some cc =>
    rw [finish_some, crash_idle]
    obtain ⟨h1, h2, h3⟩ := cut_read (P := P) L w.fs hI.pending r.entries [e] [] (by simp) hdur none (fun _ => rfl) (by simp)
      (c == 0) cc.n cc.keep cc.vanish
    refine ⟨⟨h1, ?_, trivial⟩, ?_⟩
    · rcases h3 with ⟨j, r', _, hr', _⟩ | ⟨h4, _⟩
      · exact ⟨r', hr'⟩
      · rw [h4]; exact ⟨_, read_empty⟩
    · unfold World.records
      refine records_prefix ?_
      intro hs
      refine ⟨h2 hs, ?_⟩
      rcases h3 with ⟨j, r', hj, hr', he⟩ | ⟨_, h4⟩
      · rw [hent]
        have : entriesOf P ((w.fs.runPrefix cc.n (commitPlan none (encodeFrom P (headFrom P P.genesis r.entries) [e]) (c == 0))).crash
            cc.keep cc.vanish).contents = r'.entries := by simp [entriesOf, hr']
        rw [this, he]
        exact List.prefix_append _ _
      · simp [hs] at h4

theorem inv_step_append (hI : Inv P w) (g : Nat) (e : Entry) (cut : Option Cut) :
    Inv P (w.step P (.append g e cut)) ∧ World.records P w <+: World.records P (w.step P (.append g e cut)) := by
  by_cases hg : g = w.m.gen
  · subst hg
    by_cases hr : ∃ h c, w.m.mode = .ready h c
    · obtain ⟨h, c, hm⟩ := hr
      exact inv_step_append_ready L hI hm e cut
    · rw [step_append_other w _ e cut (fun h c e' => hr ⟨h, c, e'⟩)]
      exact ⟨hI, List.prefix_refl _⟩
  · rw [step_append_stale w hg]
    exact ⟨hI, List.prefix_refl _⟩

/-- Recovery of a journal found with no bytes at all: nothing to read, nothing to settle, nothing to plan. -/
theorem inv_step_recover_empty (hI : Inv P w) (hm : w.m.mode = .opened) (hE : w.fs.contents = []) (cut : Option Cut) :
    Inv P (w.step P (.recover w.m.gen cut)) ∧ World.records P w <+: World.records P (w.step P (.recover w.m.gen cut)) := by
  rw [step_recover_opened w hm]
  have hread0 : read P w.fs.contents = some ⟨[], P.genesis, []⟩ := by rw [hE]; exact read_empty
  simp only [recoverPlan, hE, read_empty, ite_true, Mode.isBusy]
  cases cut with
  | none =>
    rw [finish_none, acked_busy]
    simp only [Fs.runAll, List.foldl_nil]
    refine ⟨⟨hI.pending, ⟨_, hread0⟩, ?_⟩, List.prefix_refl _⟩
    exact ⟨_, hread0, rfl, rfl, rfl, Or.inr rfl⟩
  | some cc =>
    rw [finish_some, crash_idle]
    simp only [Fs.runPrefix, List.take_nil, List.foldl_nil]
    obtain ⟨h1, h2, h3⟩ := crash_fs w.fs hI.pending ⟨_, hread0⟩ cc.keep cc.vanish
    refine ⟨⟨h1, h2, trivial⟩, ?_⟩
    unfold World.records
    refine records_prefix ?_
    intro hs
    rw [h3 hs]
    exact ⟨hs, List.prefix_refl _⟩

theorem inv_step_recover_data (hI : Inv P w) (hm : w.m.mode = .opened) (hE : w.fs.contents ≠ []) (cut : Option Cut) :
    Inv P (w.step P (.recover w.m.gen cut)) ∧ World.records P w <+: World.records P (w.step P (.recover w.m.gen cut)) := by
  rw [step_recover_opened w hm]
  obtain ⟨r, hrd⟩ := hI.readable
  obtain ⟨hd, hnl, hh⟩ := read_inv L _ r hrd
  have hent : entriesOf P w.fs.contents = r.entries := by simp [entriesOf, hrd]
  have hdur : w.fs.durable = encodeFrom P P.genesis r.entries ++ r.tail := by
    rw [← contents_of_pending_nil hI.pending]; exact hd
  have hgood : w.fs.contents.length - r.tail.length = (encodeFrom P P.genesis r.entries).length := by
    rw [hd]; simp
  simp only [recoverPlan, hrd, hE, ite_false, ite_true, Mode.isBusy, hh, hgood]
  generalize settleEntries r.entries = ss
  cases cut with
  | none =>
    rw [finish_none, acked_busy]
    have hfull := full_run (P := P) w.fs hI.pending r.entries ss r.tail hdur (some (encodeFrom P P.genesis r.entries).length)
      (by simp) (fun n h => (Option.some.inj h).symm) true
    rw [hfull]
    have hread := read_encode L (r.entries ++ ss) [] (by simp)
    have hread' : read P (encodeFrom P P.genesis (r.entries ++ ss)) =
        some ⟨r.entries ++ ss, headFrom P P.genesis (r.entries ++ ss), []⟩ := by simpa using hread
    refine ⟨⟨rfl, ⟨_, by simpa [Fs.contents] using hread'⟩, ?_⟩, ?_⟩
    · refine ⟨_, by simpa [Fs.contents] using hread', rfl, ?_, by simp, Or.inl (by simp)⟩
      simp [headFrom_append]
    · unfold World.records
      refine records_prefix ?_
      intro _
      refine ⟨by simp, ?_⟩
      rw [hent]
      have : entriesOf P (Fs.contents ⟨encodeFrom P P.genesis (r.entries ++ ss), [], w.fs.dirSafe || true⟩) =
          r.entries ++ ss := by simp [entriesOf, Fs.contents, hread']
      rw [this]
      exact List.prefix_append _ _
  | some cc =>
    rw [finish_some, crash_idle]
    obtain ⟨h1, h2, h3⟩ := cut_read (P := P) L w.fs hI.pending r.entries ss r.tail hnl hdur
      (some (encodeFrom P P.genesis r.entries).length) (by simp) (fun n h => (Option.some.inj h).symm)
      true cc.n cc.keep cc.vanish
    refine ⟨⟨h1, ?_, trivial⟩, ?_⟩
    · rcases h3 with ⟨j, r', _, hr', _⟩ | ⟨h4, _⟩
      · exact ⟨r', hr'⟩
      · rw [h4]; exact ⟨_, read_empty⟩
    · unfold World.records
      refine records_prefix ?_
      intro hs
      refine ⟨h2 hs, ?_⟩
      rcases h3 with ⟨j, r', hj, hr', he⟩ | ⟨_, h4⟩
      · rw [hent]
        have : entriesOf P ((w.fs.runPrefix cc.n (commitPlan (some (encodeFrom P P.genesis r.entries).length)
            (encodeFrom P (headFrom P P.genesis r.entries) ss) true)).crash cc.keep cc.vanish).contents = r'.entries := by
          simp [entriesOf, hr']
        rw [this, he]
        exact List.prefix_append _ _
      · simp [hs] at h4

theorem inv_step_recover (hI : Inv P w) (g : Nat) (cut : Option Cut) :
    Inv P (w.step P (.recover g cut)) ∧ World.records P w <+: World.records P (w.step P (.recover g cut)) := by
  by_cases hg : g = w.m.gen
  · subst hg
    by_cases hm : w.m.mode = .opened
    · by_cases hE : w.fs.contents = []
      · exact inv_step_recover_empty L hI hm hE cut
      · exact inv_step_recover_data L hI hm hE cut
    · rw [step_recover_other w _ cut hm]
      exact ⟨hI, List.prefix_refl _⟩
  · rw [step_recover_stale w hg]
    exact ⟨hI, List.prefix_refl _⟩

/-- **Append-only, one event at a time** (theorem (a)): every event of the system, with any crash point, keeps the invariant, and every
record of the journal before it is a record of the journal after it. -/
theorem inv_step (hI : Inv P w) (ev : WEvent) :
    Inv P (w.step P ev) ∧ World.records P w <+: World.records P (w.step P ev) := by
  cases ev with
  | takeOver => exact inv_step_takeOver L hI
  | crash k v => exact inv_step_crash L hI k v
  | recover g cut => exact inv_step_recover L hI g cut
  | append g e cut => exact inv_step_append L hI g e cut

end Lawful

end VbmJournal
