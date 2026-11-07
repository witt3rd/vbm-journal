import VbmJournalProofs.Laws
/-! # Chain integrity (theorem (b))

**Plain statements.**

* `read_encode`: a journal made only by appends verifies, and reads back as the entries that were appended, with the head `headFrom`.
* `headFrom_inj` and `head_binds`: the head binds the whole journal: two journals with the same head hold the same entries (so an edit
  that verifies changes the head).
* `verify_only_prefix`: lines that are all lines of a journal verify only if they are a prefix of it. So a journal whose records were
  reordered, duplicated, or deleted from the middle fails verification (`perm_verifies_only_if_same`). Cutting off the tail
  verifies (a chain alone cannot tell a shorter journal from the real one): that is what an anchor is for.
* `edit_fails`: a record whose body is edited and whose digest is left alone fails verification.
* `anchored_unique`: against an anchor (the head after `n` records, which lung signs: slice 2), every journal that verifies has the
  same first `n` entries; a journal cut below `n` records fails it (`anchored_short_fails`).

Digest collision resistance is the law `link_binds` (`Params.Lawful`), a hypothesis. -/
namespace VbmJournal

theorem nl_ne_sp : nl ≠ sp := by decide

/-! ## Lines and bytes -/

theorem parseLines_noNl {t : Bytes} (h : nl ∉ t) : parseLines t = ([], t) := by
  induction t with
  | nil => rfl
  | cons b t ih =>
    have hb : b ≠ nl := fun e => h (by simp [e])
    have ht : nl ∉ t := fun e => h (by simp [e])
    simp [parseLines, hb, ih ht]

theorem parseLines_frame {l : Bytes} (rest : Bytes) (h : nl ∉ l) :
    parseLines (l ++ nl :: rest) = (l :: (parseLines rest).1, (parseLines rest).2) := by
  induction l with
  | nil => simp [parseLines]
  | cons b l ih =>
    have hb : b ≠ nl := fun e => h (by simp [e])
    have hl : nl ∉ l := fun e => h (by simp [e])
    simp [parseLines, hb, ih hl]

/-- The bytes of a list of lines, each with its newline. -/
def flat : List Bytes → Bytes
  | [] => []
  | l :: ls => frame l ++ flat ls

theorem parseLines_spec : ∀ (d : Bytes) (ls : List Bytes) (t : Bytes), parseLines d = (ls, t) → d = flat ls ++ t ∧ nl ∉ t := by
  intro d
  induction d with
  | nil => intro ls t h; simp [parseLines] at h; obtain ⟨rfl, rfl⟩ := h; simp [flat]
  | cons b rest ih =>
    intro ls t h
    rcases hr : parseLines rest with ⟨ls1, t1⟩
    obtain ⟨hrest, ht1⟩ := ih ls1 t1 hr
    by_cases hb : b = nl
    · simp only [parseLines, hr, hb, ite_true, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [flat, frame, hb]
      exact ⟨hrest, ht1⟩
    · cases ls1 with
      | nil =>
        simp only [parseLines, hr, hb, ite_false, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [flat] at hrest
        simp [flat, hrest, ht1]
        exact fun e => hb e.symm
      | cons l ls2 =>
        simp only [parseLines, hr, hb, ite_false, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [flat, frame] at hrest ⊢
        simp [hrest, ht1]

theorem splitLine_sealed {d : Digest} (body : Bytes) (h : sp ∉ d) : splitLine (d ++ sp :: body) = some (d, body) := by
  induction d with
  | nil => simp [splitLine]
  | cons b d ih =>
    have hb : b ≠ sp := fun e => h (by simp [e])
    have hd : sp ∉ d := fun e => h (by simp [e])
    simp [splitLine, hb, ih hd]

theorem splitLine_inv : ∀ (l : Bytes) (d body : Bytes), splitLine l = some (d, body) → l = d ++ sp :: body ∧ sp ∉ d := by
  intro l
  induction l with
  | nil => intro d body h; simp [splitLine] at h
  | cons b rest ih =>
    intro d body h
    by_cases hb : b = sp
    · simp [splitLine, hb] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [hb]
    · simp only [splitLine, hb, ite_false] at h
      cases hr : splitLine rest with
      | none => simp [hr] at h
      | some p =>
        obtain ⟨d1, b1⟩ := p
        simp [hr] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨h1, h2⟩ := ih d1 b1 hr
        simp [h1, h2]
        exact fun e => hb e.symm

/-! ## Entries and lines -/

theorem headFrom_append (P : Params) (prev : Digest) (xs ys : List Entry) :
    headFrom P prev (xs ++ ys) = headFrom P (headFrom P prev xs) ys := by
  induction xs generalizing prev with
  | nil => rfl
  | cons x xs ih => simp [headFrom, ih]

theorem headFrom_snoc (P : Params) (prev : Digest) (xs : List Entry) (e : Entry) :
    headFrom P prev (xs ++ [e]) = P.link (headFrom P prev xs) (P.enc e) := by
  rw [headFrom_append]; rfl

theorem encodeFrom_append (P : Params) (prev : Digest) (xs ys : List Entry) :
    encodeFrom P prev (xs ++ ys) = encodeFrom P prev xs ++ encodeFrom P (headFrom P prev xs) ys := by
  induction xs generalizing prev with
  | nil => rfl
  | cons x xs ih => simp [encodeFrom, headFrom, ih]

theorem encodeFrom_eq_flat (P : Params) (prev : Digest) (es : List Entry) : encodeFrom P prev es = flat (sealAll P prev es) := by
  induction es generalizing prev with
  | nil => rfl
  | cons e es ih => simp [encodeFrom, sealAll, flat, ih]

theorem sealAll_append (P : Params) (prev : Digest) (xs ys : List Entry) :
    sealAll P prev (xs ++ ys) = sealAll P prev xs ++ sealAll P (headFrom P prev xs) ys := by
  induction xs generalizing prev with
  | nil => rfl
  | cons x xs ih => simp [sealAll, headFrom, ih]

theorem sealAll_length {P : Params} (prev : Digest) (es : List Entry) : (sealAll P prev es).length = es.length := by
  induction es generalizing prev with
  | nil => rfl
  | cons _ _ ih => simp [sealAll, ih]


theorem rev_induction {α : Type} {motive : List α → Prop} (nil : motive [])
    (snoc : ∀ xs x, motive xs → motive (xs ++ [x])) : ∀ l, motive l := by
  suffices h : ∀ n (l : List α), l.length = n → motive l from fun l => h _ l rfl
  intro n
  induction n with
  | zero => intro l hl; cases l with | nil => exact nil | cons => simp at hl
  | succ n ih =>
    intro l hl
    rcases List.eq_nil_or_concat l with rfl | ⟨l', b, rfl⟩
    · simp at hl
    · simp only [List.concat_eq_append, List.length_append, List.length_singleton] at hl ⊢
      exact snoc l' b (ih l' (by omega))

variable {P : Params}

section Lawful
variable (L : P.Lawful)
include L

theorem lineOf_clean (prev : Digest) (e : Entry) : nl ∉ lineOf P prev e := by
  have h1 := (L.link_clean prev (P.enc e)).1
  have h2 := L.enc_clean e
  simp only [lineOf, List.mem_append, List.mem_cons, not_or]
  exact ⟨h1, Ne.symm nl_ne_sp |>.symm, h2⟩

theorem splitLine_lineOf (prev : Digest) (e : Entry) :
    splitLine (lineOf P prev e) = some (P.link prev (P.enc e), P.enc e) :=
  splitLine_sealed _ (L.link_clean _ _).2

theorem lineOf_inj {a b : Digest} {e e' : Entry} (h : lineOf P a e' = lineOf P b e) : a = b ∧ e' = e := by
  have := congrArg splitLine h
  rw [splitLine_lineOf L, splitLine_lineOf L] at this
  simp only [Option.some.injEq, Prod.mk.injEq] at this
  obtain ⟨h1, h2⟩ := this
  have h3 := L.enc_inj h2
  subst h3
  exact ⟨(L.link_binds _ _ _ _ h1).1, rfl⟩

/-- Entries that were sealed verify. -/
theorem verifyFrom_sealAll (prev : Digest) (es : List Entry) :
    verifyFrom P prev (sealAll P prev es) = some (es, headFrom P prev es) := by
  induction es generalizing prev with
  | nil => rfl
  | cons e es ih => simp [sealAll, verifyFrom, splitLine_lineOf L, L.dec_enc, ih, headFrom]

/-- What verifies is exactly the lines that were sealed from the entries it returns. -/
theorem verifyFrom_inv : ∀ (ls : List Bytes) (prev : Digest) (es : List Entry) (h : Digest),
    verifyFrom P prev ls = some (es, h) → ls = sealAll P prev es ∧ h = headFrom P prev es := by
  intro ls
  induction ls with
  | nil =>
    intro prev es h hv
    simp [verifyFrom] at hv
    obtain ⟨rfl, rfl⟩ := hv
    simp [sealAll, headFrom]
  | cons l ls ih =>
    intro prev es h hv
    simp only [verifyFrom] at hv
    cases hs : splitLine l with
    | none => simp [hs] at hv
    | some p =>
      obtain ⟨d, body⟩ := p
      simp only [hs] at hv
      by_cases hd : P.link prev body = d
      · simp only [hd, ite_true] at hv
        cases hde : P.dec body with
        | none => simp [hde] at hv
        | some e =>
          simp only [hde] at hv
          cases hr : verifyFrom P d ls with
          | none => simp [hr] at hv
          | some q =>
            obtain ⟨es1, h1⟩ := q
            simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hv
            obtain ⟨rfl, rfl⟩ := hv
            obtain ⟨ih1, ih2⟩ := ih d es1 h1 hr
            have hb := L.enc_of_dec _ _ hde
            obtain ⟨hl, _⟩ := splitLine_inv l d body hs
            subst hb
            subst hd
            simp [sealAll, headFrom, lineOf, hl, ih1, ih2]
      · simp [hd] at hv

theorem parseLines_encodeFrom (prev : Digest) (es : List Entry) (t : Bytes) (ht : nl ∉ t) :
    parseLines (encodeFrom P prev es ++ t) = (sealAll P prev es, t) := by
  induction es generalizing prev with
  | nil => simpa [encodeFrom, sealAll] using parseLines_noNl ht
  | cons e es ih =>
    simp only [encodeFrom, frame, sealAll, List.append_assoc, List.cons_append, List.nil_append]
    rw [parseLines_frame _ (lineOf_clean L _ _), ih]

/-- **A journal made only by appends verifies**, and reads back as the entries that were appended; a torn tail after them is dropped. -/
theorem read_encode (es : List Entry) (t : Bytes) (ht : nl ∉ t) :
    read P (encodeFrom P P.genesis es ++ t) = some ⟨es, headFrom P P.genesis es, t⟩ := by
  simp [read, parseLines_encodeFrom L _ _ _ ht, verifyFrom_sealAll L]

/-- What a successful read says about the bytes. -/
theorem read_inv (d : Bytes) (r : Read) (h : read P d = some r) :
    d = encodeFrom P P.genesis r.entries ++ r.tail ∧ nl ∉ r.tail ∧ r.head = headFrom P P.genesis r.entries := by
  unfold read at h
  rcases hp : parseLines d with ⟨ls, t⟩
  simp only [hp] at h
  cases hv : verifyFrom P P.genesis ls with
  | none => simp [hv] at h
  | some q =>
    obtain ⟨es, hh⟩ := q
    simp only [hv, Option.map_some, Option.some.injEq] at h
    subst h
    obtain ⟨hs1, hs2⟩ := verifyFrom_inv L ls _ es hh hv
    obtain ⟨hd, hnl⟩ := parseLines_spec d ls t hp
    refine ⟨?_, hnl, hs2⟩
    rw [hd, hs1, encodeFrom_eq_flat]

/-- A write cut anywhere leaves a verifying journal: the entries before, then the first `j` complete entries of what was written,
then a torn tail. -/
theorem read_partial : ∀ (ss es : List Entry) (k : Nat), ∃ j t, j ≤ ss.length ∧ nl ∉ t ∧
    read P (encodeFrom P P.genesis es ++ (encodeFrom P (headFrom P P.genesis es) ss).take k) =
      some ⟨es ++ ss.take j, headFrom P P.genesis (es ++ ss.take j), t⟩ := by
  intro ss
  induction ss with
  | nil =>
    intro es k
    refine ⟨0, [], by simp, by simp, ?_⟩
    simpa [encodeFrom] using read_encode L es [] (by simp)
  | cons s ss ih =>
    intro es k
    by_cases hk : k < (frame (lineOf P (headFrom P P.genesis es) s)).length
    · have hnl : nl ∉ (frame (lineOf P (headFrom P P.genesis es) s)).take k := by
        have hlen : (lineOf P (headFrom P P.genesis es) s).length + 1 = (frame (lineOf P (headFrom P P.genesis es) s)).length := by simp [frame]
        have : (frame (lineOf P (headFrom P P.genesis es) s)).take k = (lineOf P (headFrom P P.genesis es) s).take k := by
          simp only [frame]; rw [List.take_append_of_le_length (by omega)]
        rw [this]
        exact fun hm => lineOf_clean L _ _ (List.mem_of_mem_take hm)
      refine ⟨0, _, by simp, hnl, ?_⟩
      have : (encodeFrom P (headFrom P P.genesis es) (s :: ss)).take k =
          (frame (lineOf P (headFrom P P.genesis es) s)).take k := by
        simp only [encodeFrom]; rw [List.take_append_of_le_length (by omega)]
      rw [this]
      simpa using read_encode L es _ hnl
    · have hk := Nat.le_of_not_lt hk
      obtain ⟨j, t, hj, ht, hr⟩ := ih (es ++ [s]) (k - (frame (lineOf P (headFrom P P.genesis es) s)).length)
      refine ⟨j + 1, t, by simpa using hj, ht, ?_⟩
      have e1 : (encodeFrom P (headFrom P P.genesis es) (s :: ss)).take k =
          frame (lineOf P (headFrom P P.genesis es) s) ++
            (encodeFrom P (P.link (headFrom P P.genesis es) (P.enc s)) ss).take
              (k - (frame (lineOf P (headFrom P P.genesis es) s)).length) := by
        simp only [encodeFrom]
        rw [List.take_append, List.take_of_length_le hk]
      rw [e1]
      rw [headFrom_snoc] at hr
      have e2 : encodeFrom P P.genesis es ++ (frame (lineOf P (headFrom P P.genesis es) s) ++
            (encodeFrom P (P.link (headFrom P P.genesis es) (P.enc s)) ss).take
              (k - (frame (lineOf P (headFrom P P.genesis es) s)).length)) =
          encodeFrom P P.genesis (es ++ [s]) ++ (encodeFrom P (P.link (headFrom P P.genesis es) (P.enc s)) ss).take
              (k - (frame (lineOf P (headFrom P P.genesis es) s)).length) := by
        simp [encodeFrom_append, encodeFrom]
      rw [e2, hr]
      simp

/-! ## The head binds the journal -/

theorem headFrom_inj : ∀ (es es' : List Entry), headFrom P P.genesis es = headFrom P P.genesis es' → es = es' := by
  intro es
  induction es using rev_induction with
  | nil =>
    intro es' h
    rcases List.eq_nil_or_concat es' with rfl | ⟨ys, y, hy⟩
    · rfl
    · rw [List.concat_eq_append] at hy; subst hy
      rw [headFrom_snoc] at h
      exact absurd h.symm (L.link_ne_genesis _ _)
  | snoc xs x ih =>
    intro es' h
    rcases List.eq_nil_or_concat es' with rfl | ⟨ys, y, hy⟩
    · rw [headFrom_snoc] at h
      exact absurd h (L.link_ne_genesis _ _)
    · rw [List.concat_eq_append] at hy; subst hy
      rw [headFrom_snoc, headFrom_snoc] at h
      obtain ⟨h1, h2⟩ := L.link_binds _ _ _ _ h
      rw [ih ys h1, L.enc_inj h2]

/-- **The head binds the journal**: two journals that verify and have the same head hold the same entries, and so the same bytes. -/
theorem head_binds {a b : Bytes} {r r' : Read} (ha : read P a = some r) (hb : read P b = some r')
    (hh : r.head = r'.head) (hta : r.tail = []) (htb : r'.tail = []) : a = b := by
  obtain ⟨ea, _, ha2⟩ := read_inv L a r ha
  obtain ⟨eb, _, hb2⟩ := read_inv L b r' hb
  rw [ha2, hb2] at hh
  have := headFrom_inj L _ _ hh
  rw [ea, eb, this, hta, htb]

/-- An edit that verifies changes the head: different entries, different heads. -/
theorem edit_changes_head {es es' : List Entry} (h : es ≠ es') :
    headFrom P P.genesis es ≠ headFrom P P.genesis es' := fun e => h (headFrom_inj L _ _ e)

/-! ## Cut, reordered, deleted, duplicated or edited records fail -/

/-- A line sealed after `pre`, found among the lines sealed from `pre0` onward, is at the position that `pre` says. -/
theorem mem_sealAll : ∀ (es0 pre0 pre : List Entry) (e' : Entry),
    lineOf P (headFrom P P.genesis pre) e' ∈ sealAll P (headFrom P P.genesis pre0) es0 →
    ∃ x y, es0 = x ++ e' :: y ∧ pre = pre0 ++ x := by
  intro es0
  induction es0 with
  | nil => intro pre0 pre e' h; simp [sealAll] at h
  | cons e es1 ih =>
    intro pre0 pre e' h
    simp only [sealAll, List.mem_cons] at h
    rcases h with h | h
    · obtain ⟨h1, h2⟩ := lineOf_inj L h
      have := headFrom_inj L _ _ h1
      subst this; subst h2
      exact ⟨[], es1, rfl, by simp⟩
    · rw [← headFrom_snoc] at h
      obtain ⟨x, y, hx, hp⟩ := ih (pre0 ++ [e]) pre e' h
      exact ⟨e :: x, y, by simp [hx], by simp [hp]⟩

/-- **Reordered, duplicated or deleted records fail.** Lines that all come from a journal's lines, and that verify, are a prefix of it. -/
theorem verify_only_prefix {es es' : List Entry} {ls' : List Bytes} {h : Digest}
    (hv : verifyFrom P P.genesis ls' = some (es', h)) (hsub : ∀ l ∈ ls', l ∈ sealAll P P.genesis es) :
    ∃ z, es = es' ++ z := by
  obtain ⟨hl, _⟩ := verifyFrom_inv L _ _ _ _ hv
  subst hl
  have key : ∀ (es' pre : List Entry), (∀ l ∈ sealAll P (headFrom P P.genesis pre) es', l ∈ sealAll P P.genesis es) →
      (∃ z, es = pre ++ z) → ∃ z', es = pre ++ es' ++ z' := by
    intro es'
    induction es' with
    | nil => intro pre _ ⟨z, hz⟩; exact ⟨z, by simpa using hz⟩
    | cons e' rest ih =>
      intro pre hs _
      have h1 := hs (lineOf P (headFrom P P.genesis pre) e') (by simp [sealAll])
      obtain ⟨x, y, hx, hp⟩ := mem_sealAll L es [] pre e' (by simpa [headFrom] using h1)
      have hp' : pre = x := by simpa using hp
      subst hp'
      have h2 : ∀ l ∈ sealAll P (headFrom P P.genesis (pre ++ [e'])) rest, l ∈ sealAll P P.genesis es := by
        intro l hl
        apply hs
        rw [headFrom_snoc] at hl
        simp [sealAll, hl]
      obtain ⟨z', hz'⟩ := ih (pre ++ [e']) h2 ⟨y, by simp [hx]⟩
      exact ⟨z', by simpa using hz'⟩
  obtain ⟨z, hz⟩ := key es' [] (by simpa [headFrom] using hsub) ⟨es, by simp⟩
  exact ⟨z, by simpa using hz⟩

/-- A reordering of a journal's lines that verifies is the journal itself. -/
theorem perm_verifies_only_if_same {es es' : List Entry} {ls' : List Bytes} {h : Digest}
    (hv : verifyFrom P P.genesis ls' = some (es', h)) (hp : ls'.Perm (sealAll P P.genesis es)) : ls' = sealAll P P.genesis es := by
  obtain ⟨z, hz⟩ := verify_only_prefix L hv (fun l hl => hp.subset hl)
  obtain ⟨hl, _⟩ := verifyFrom_inv L _ _ _ _ hv
  have hlen := hp.length_eq
  rw [hl, sealAll_length, sealAll_length, hz] at hlen
  simp only [List.length_append] at hlen
  have : z = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst this
  rw [hl, hz]; simp

theorem verifyFrom_sealAll_append (prev : Digest) (pre : List Entry) (rest : List Bytes) :
    verifyFrom P prev (sealAll P prev pre ++ rest) =
      (verifyFrom P (headFrom P prev pre) rest).map fun q => (pre ++ q.1, q.2) := by
  induction pre generalizing prev with
  | nil => cases h : verifyFrom P prev rest <;> simp [sealAll, headFrom, h]
  | cons e pre ih =>
    simp only [sealAll, List.cons_append, verifyFrom, splitLine_lineOf L, L.dec_enc, ite_true, headFrom]
    rw [ih]
    cases verifyFrom P (headFrom P (P.link prev (P.enc e)) pre) rest <;> simp

/-- **An edited record fails.** A record whose body is changed and whose digest is left alone fails verification
(an edit that also recomputes the digest breaks the next record's digest, or, at the end, changes the head: `edit_changes_head`). -/
theorem edit_fails (pre post : List Entry) (e : Entry) (b' : Bytes) (hb : b' ≠ P.enc e) :
    verifyFrom P P.genesis (sealAll P P.genesis pre ++
      (P.link (headFrom P P.genesis pre) (P.enc e) ++ sp :: b') :: sealAll P (headFrom P P.genesis (pre ++ [e])) post) = none := by
  rw [verifyFrom_sealAll_append L]
  simp only [verifyFrom, splitLine_sealed _ (L.link_clean _ _).2]
  have : P.link (headFrom P P.genesis pre) b' ≠ P.link (headFrom P P.genesis pre) (P.enc e) := fun h => hb (L.link_binds _ _ _ _ h).2
  simp [this]

/-! ## Anchors: the head after `n` records, signed in lung (the HMAC file is slice 2) -/

/-- The bytes are a journal that verifies, has at least `n` entries, and whose head after `n` is `d`. -/
def Anchored (P : Params) (n : Nat) (d : Digest) (bytes : Bytes) : Prop :=
  ∃ r, read P bytes = some r ∧ n ≤ r.entries.length ∧ headFrom P P.genesis (r.entries.take n) = d

/-- **A cut fails the anchor, an edit before it fails it**: every journal that holds the anchor has the same first `n` entries. -/
theorem anchored_unique {n : Nat} {d : Digest} {a b : Bytes} (ha : Anchored P n d a) (hb : Anchored P n d b) :
    ∃ ra rb, read P a = some ra ∧ read P b = some rb ∧ ra.entries.take n = rb.entries.take n := by
  obtain ⟨ra, h1, _, h2⟩ := ha
  obtain ⟨rb, h3, _, h4⟩ := hb
  exact ⟨ra, rb, h1, h3, headFrom_inj L _ _ (h2.trans h4.symm)⟩

omit L in
/-- A journal with fewer than `n` records fails an anchor at `n`. -/
theorem anchored_short_fails {n : Nat} {d : Digest} {b : Bytes} {r : Read} (hr : read P b = some r)
    (hs : r.entries.length < n) : ¬ Anchored P n d b := by
  rintro ⟨r', h1, h2, _⟩
  rw [hr] at h1
  cases h1
  omega

/-- A journal as appended holds the anchor of its own first `n` entries. -/
theorem anchored_honest (es : List Entry) (n : Nat) (hn : n ≤ es.length) (t : Bytes) (ht : nl ∉ t) :
    Anchored P n (headFrom P P.genesis (es.take n)) (encodeFrom P P.genesis es ++ t) :=
  ⟨_, read_encode L es t ht, hn, rfl⟩

end Lawful

end VbmJournal
