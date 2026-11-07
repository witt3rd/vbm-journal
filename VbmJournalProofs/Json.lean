import VbmJournalProofs.Space
import VbmJournalProofs.Real
/-! # The JSON-lines journal meets the laws, if SHA-256 is collision resistant

`Params.jsonl label` (`VbmJournal.Json`) is the journal of a host that keeps JSON lines with a digest chain. `jsonl_lawful` says it meets `Params.Lawful`, so that every theorem of slices 1
and 2 holds of it, **given that `sha256` is collision resistant** (`Sha256.CollisionFree`, the hypothesis of `real_lawful` too) and that the label is a text the chain input cannot be
mistaken for: it has no newline and does not begin with the byte 255 (a text label does not).

* **The digest binds** for every input, not only for the digests a journal holds: a hash input is `prev "\n" body` with `prev` a digest without a newline, so (`prev`, `body`)
  is its first newline's two sides (the same argument as the prefix code of `chainInput` in slice 2); a `prev` with a newline is hashed in an encoding with no newline at all.
* **The codec** round-trips and is canonical: a host record is a body (`bodyWf`: `{"`, no newline, not `{"vbm"`), a library entry is `{"vbm":"<unary>"}`; the two never overlap.
* **The line** is cut back by position: the digest is hex, so it ends at the first quote; the body is `{` and what follows `",`.
* **The signature file** reads back in the form it is written. -/
namespace VbmJournal

/-! ## Small lemmas on the format -/

theorem startsL_append (p r : Bytes) : startsL p (p ++ r) = true := by
  simp [startsL]

theorem startsL_inv {p l : Bytes} (h : startsL p l = true) : l = p ++ l.drop p.length := by
  simp only [startsL, beq_iff_eq] at h
  calc l = l.take p.length ++ l.drop p.length := (List.take_append_drop _ _).symm
    _ = p ++ l.drop p.length := by rw [h]

theorem stripSuf_append (s m : Bytes) : stripSuf s (m ++ s) = some m := by
  simp [stripSuf]

theorem stripSuf_inv {s l m : Bytes} (h : stripSuf s l = some m) : l = m ++ s := by
  unfold stripSuf at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
    simp only [Option.some.injEq] at h
    subst h
    calc l = l.take (l.length - s.length) ++ l.drop (l.length - s.length) := (List.take_append_drop _ _).symm
      _ = _ := by rw [hc.2]
  · simp at h

theorem cutAt_find (x : UInt8) (rest : Bytes) : ∀ (a : Bytes), x ∉ a → cutAt x (a ++ x :: rest) = some (a, rest) := by
  intro a
  induction a with
  | nil => intro _; simp [cutAt]
  | cons b a ih =>
    intro h
    have hb : b ≠ x := fun e => h (by simp [e])
    have ha : x ∉ a := fun e => h (by simp [e])
    simp [cutAt, hb, ih ha]

theorem jCut_inv : ∀ (r d b : Bytes), jCut r = some (d, b) → ∃ t, r = d ++ 34 :: 44 :: t ∧ b = 123 :: t ∧ 34 ∉ d := by
  intro r
  induction r with
  | nil => intro d b h; simp [jCut] at h
  | cons c r ih =>
    intro d b h
    by_cases hc : c = 34
    · subst hc
      cases r with
      | nil => simp [jCut] at h
      | cons x xs =>
        by_cases hx : x = 44
        · subst hx
          simp [jCut] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨xs, by simp⟩
        · simp [jCut, hx] at h
    · simp only [jCut, hc, ite_false] at h
      cases hr : jCut r with
      | none => simp [hr] at h
      | some q =>
        obtain ⟨d1, b1⟩ := q
        simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨t, h1, h2, h3⟩ := ih d1 b1 hr
        refine ⟨t, by simp [h1], h2, ?_⟩
        simp only [List.mem_cons, not_or]
        exact ⟨fun e => hc e.symm, h3⟩

theorem append_nl_inj : ∀ (p p' b b' : Bytes), nl ∉ p → nl ∉ p' → p ++ nl :: b = p' ++ nl :: b' → p = p' ∧ b = b' := by
  intro p
  induction p with
  | nil =>
    intro p' b b' _ hp' h
    cases p' with
    | nil => simpa using h
    | cons y ys => simp at h; exact absurd h.1.symm (fun e => hp' (by simp [e]))
  | cons x xs ih =>
    intro p' b b' hp hp' h
    cases p' with
    | nil => simp at h; exact absurd h.1 (fun e => hp (by simp [e]))
    | cons y ys =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h2⟩ := h
      obtain ⟨h3, h4⟩ := ih ys b b' (fun e => hp (by simp [e])) (fun e => hp' (by simp [e])) h2
      subst h3
      exact ⟨rfl, h4⟩

/-- A well-formed host record: its shape. -/
theorem bodyWf_shape {l : Bytes} (h : bodyWf l = true) : (∃ t, l = 123 :: 34 :: t) ∧ nl ∉ l ∧ startsL jVbm l = false := by
  refine ⟨?_, bodyWf_nl h, ?_⟩
  · simp only [bodyWf, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨h1, _⟩, _⟩ := h
    match l, h1 with
    | a :: b :: t, h1 => simp at h1; obtain ⟨rfl, rfl⟩ := h1; exact ⟨t, rfl⟩
  · simp only [bodyWf, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨⟨_, h2⟩, _⟩ := h
    cases hs : startsL jVbm l
    · rfl
    · exfalso
      apply h2
      simp only [startsL, beq_iff_eq] at hs
      have h6 : l.take 6 = (l.take 8).take 6 := by rw [List.take_take]; rfl
      rw [h6]
      simp only [jVbm, List.length_cons, List.length_nil] at hs
      rw [hs]
      rfl

/-! ## The codec -/

theorem jLib_some {m : Bytes} {e : Entry} (h : jLib m = some e) : decUnary m = some e ∧ ∀ b, e ≠ Entry.body b := by
  unfold jLib at h
  cases hd : decUnary m with
  | none => simp [hd] at h
  | some x =>
    cases x with
    | body b => simp [hd] at h
    | note n => simp [hd] at h; subst h; exact ⟨rfl, by intro b h; cases h⟩
    | call n => simp [hd] at h; subst h; exact ⟨rfl, by intro b h; cases h⟩
    | done n i => simp [hd] at h; subst h; exact ⟨rfl, by intro b h; cases h⟩

theorem jLib_encUnary (e : Entry) (h : ∀ b, e ≠ Entry.body b) : jLib (encUnary e) = some e := by
  unfold jLib
  rw [decUnary_encUnary]
  cases e with
  | body b => exact absurd rfl (h b)
  | note n => rfl
  | call n => rfl
  | done n i => rfl

theorem jEnc_lib (e : Entry) (h : ∀ b, e ≠ Entry.body b) : jEnc e = jVbm ++ encUnary e ++ jEnd := by
  cases e with
  | body b => exact absurd rfl (h b)
  | note n => rfl
  | call n => rfl
  | done n i => rfl

theorem jVbm_length : jVbm.length = 8 := rfl

theorem jDec_jEnc (e : Entry) : jDec (jEnc e) = some e := by
  by_cases hb : ∃ b, e = Entry.body b
  · obtain ⟨b, rfl⟩ := hb
    obtain ⟨bs, hw⟩ := b
    have hs := bodyWf_shape hw
    simp only [jEnc, jDec, hs.2.2, Bool.false_eq_true, ite_false]
    simp [hw]
  · have hb' : ∀ b, e ≠ Entry.body b := fun b h => hb ⟨b, h⟩
    rw [jEnc_lib e hb']
    unfold jDec
    have hv : startsL jVbm (jVbm ++ encUnary e ++ jEnd) = true := by
      rw [List.append_assoc]; exact startsL_append _ _
    have hd : (jVbm ++ encUnary e ++ jEnd).drop 8 = encUnary e ++ jEnd := by
      rw [List.append_assoc, ← jVbm_length]; exact List.drop_left' rfl
    simp only [hv, ite_true, hd, stripSuf_append, Option.bind_some]
    exact jLib_encUnary e hb'

theorem jEnc_jDec {l : Bytes} {e : Entry} (h : jDec l = some e) : jEnc e = l := by
  unfold jDec at h
  by_cases hv : startsL jVbm l = true
  · simp only [hv, ite_true] at h
    cases hs : stripSuf jEnd (l.drop 8) with
    | none => simp [hs] at h
    | some m =>
      simp only [hs, Option.bind_some] at h
      obtain ⟨h1, h2⟩ := jLib_some h
      rw [jEnc_lib e h2, encUnary_decUnary m e h1]
      have := startsL_inv hv
      have h3 := stripSuf_inv hs
      rw [jVbm_length] at this
      rw [List.append_assoc, ← h3]
      exact this.symm
  · simp only [Bool.not_eq_true] at hv
    simp only [hv, Bool.false_eq_true, ite_false] at h
    by_cases hw : bodyWf l = true
    · simp [hw] at h
      subst h
      exact toList_toByteArray l
    · simp [hw] at h

theorem jEnc_clean (e : Entry) : nl ∉ jEnc e := by
  by_cases hb : ∃ b, e = Entry.body b
  · obtain ⟨b, rfl⟩ := hb
    exact bodyWf_nl b.wf
  · have hb' : ∀ b, e ≠ Entry.body b := fun b h => hb ⟨b, h⟩
    rw [jEnc_lib e hb']
    have h1 : nl ∉ jVbm := by decide
    have h2 : nl ∉ jEnd := by decide
    intro h
    simp only [List.mem_append] at h
    rcases h with (h | h) | h
    · exact h1 h
    · exact encUnary_clean e h
    · exact h2 h

theorem jEnc_head (e : Entry) : ∃ t, jEnc e = 123 :: t := by
  by_cases hb : ∃ b, e = Entry.body b
  · obtain ⟨b, rfl⟩ := hb
    obtain ⟨t, ht⟩ := (bodyWf_shape b.wf).1
    exact ⟨34 :: t, by simpa [jEnc] using ht⟩
  · have hb' : ∀ b, e ≠ Entry.body b := fun b h => hb ⟨b, h⟩
    rw [jEnc_lib e hb']
    exact ⟨34 :: 118 :: 98 :: 109 :: 34 :: 58 :: 34 :: (encUnary e ++ jEnd), by simp [jVbm]⟩

/-! ## The line -/

theorem jFrame_of_head {d b t : Bytes} (hb : b = 123 :: t) : jFrame d b = jPre ++ d ++ 34 :: 44 :: t := by
  subst hb; simp [jFrame, jMid]

theorem jLine_clean (d : Digest) (hd : nl ∉ d) (e : Entry) : nl ∉ jFrame d (jEnc e) := by
  obtain ⟨t, ht⟩ := jEnc_head e
  rw [jFrame_of_head ht]
  have h2 := jEnc_clean e
  rw [ht] at h2
  simp only [List.mem_append, List.mem_cons, not_or]
  refine ⟨⟨by decide, hd⟩, by decide, by decide, fun h => h2 (by simp [h])⟩

theorem jSplit_jFrame (d : Digest) (hd : 34 ∉ d) (e : Entry) : jSplit (jFrame d (jEnc e)) = some (d, jEnc e) := by
  obtain ⟨t, ht⟩ := jEnc_head e
  rw [jFrame_of_head ht]
  unfold jSplit
  have h1 : startsL jPre (jPre ++ d ++ 34 :: 44 :: t) = true := by
    rw [List.append_assoc]; exact startsL_append _ _
  have h2 : (jPre ++ d ++ 34 :: 44 :: t).drop 6 = d ++ 34 :: 44 :: t := by
    rw [List.append_assoc]; exact List.drop_left' rfl
  simp only [h1, ite_true, h2]
  have := jCut_find (44 :: t) d hd
  simp only at this
  rw [this, ht]

theorem jSplit_inv {l d b : Bytes} (h : jSplit l = some (d, b)) : l = jFrame d b := by
  unfold jSplit at h
  split at h
  · rename_i hs
    obtain ⟨t, h1, h2, _⟩ := jCut_inv _ _ _ h
    have := startsL_inv hs
    have hp : jPre.length = 6 := rfl
    rw [hp] at this
    rw [jFrame_of_head h2, this, h1]
    simp
  · simp at h

/-! ## The digest -/

theorem jInput_inj {p p' b b' : Bytes} (h : jInput p b = jInput p' b') : p = p' ∧ b = b' := by
  unfold jInput at h
  by_cases hp : p.contains nl = true <;> by_cases hp' : p'.contains nl = true
  · simp only [hp, hp', ite_true, jDirty, List.cons.injEq, true_and] at h
    exact chainInput_inj _ _ _ _ (hexOf_inj _ _ h)
  · simp only [hp, hp', ite_true, Bool.false_eq_true, ite_false, jDirty] at h
    exfalso
    have : nl ∈ p' ++ nl :: b' := by simp
    rw [← h] at this
    simp only [List.mem_cons] at this
    rcases this with e | e
    · simp [nl] at e
    · exact (hexOf_clean _).1 e
  · simp only [hp, hp', ite_true, Bool.false_eq_true, ite_false, jDirty] at h
    exfalso
    have : nl ∈ p ++ nl :: b := by simp
    rw [h] at this
    simp only [List.mem_cons] at this
    rcases this with e | e
    · simp [nl] at e
    · exact (hexOf_clean _).1 e
  · simp only [Bool.not_eq_true] at hp hp'
    simp only [hp, hp', Bool.false_eq_true, ite_false] at h
    exact append_nl_inj _ _ _ _ (by simpa using hp) (by simpa using hp') h

/-! ## The signature file -/

theorem natDec_no_comma (n : Nat) : (44 : UInt8) ∉ natDec n := by
  intro h
  have := natDec_digits n _ h
  simp at this

theorem jSig_round (s : Sig) (h : (34 : UInt8) ∉ s.head) : jSigDec (jSigEnc s) = some s := by
  obtain ⟨i, hd, m⟩ := s
  simp only at h
  unfold jSigEnc jSigDec
  simp only [List.append_assoc, List.cons_append]
  have e1 : startsL jHeadK (jHeadK ++ (hd ++ 34 :: (jIdxK ++ (natDec i ++ 44 :: (jMacK ++ (m ++ jEnd)))))) = true := startsL_append _ _
  have e2 : (jHeadK ++ (hd ++ 34 :: (jIdxK ++ (natDec i ++ 44 :: (jMacK ++ (m ++ jEnd)))))).drop 9 =
      hd ++ 34 :: (jIdxK ++ (natDec i ++ 44 :: (jMacK ++ (m ++ jEnd)))) := List.drop_left' rfl
  simp only [e1, ite_true]
  rw [e2, cutAt_find 34 _ hd h]
  simp only
  have e3 : startsL jIdxK (jIdxK ++ (natDec i ++ 44 :: (jMacK ++ (m ++ jEnd)))) = true := startsL_append _ _
  have e4 : (jIdxK ++ (natDec i ++ 44 :: (jMacK ++ (m ++ jEnd)))).drop 9 = natDec i ++ 44 :: (jMacK ++ (m ++ jEnd)) := List.drop_left' rfl
  simp only [e3, ite_true]
  rw [e4, cutAt_find 44 _ _ (natDec_no_comma i)]
  simp only
  have e5 : startsL jMacK (jMacK ++ (m ++ jEnd)) = true := startsL_append _ _
  have e6 : (jMacK ++ (m ++ jEnd)).drop 7 = m ++ jEnd := List.drop_left' rfl
  simp only [e5, ite_true]
  rw [e6, stripSuf_append, parseDec_natDec]

/-! ## The laws -/

/-- **The JSON-lines journal meets the laws of the chain, the codec, the line and the signature file**, if SHA-256 is collision resistant and the label is a text label
(no newline in it, and it does not begin with the byte 255). -/
theorem jsonl_lawful (label : Bytes) (hcr : Sha256.CollisionFree) (hl : nl ∉ label) (hl2 : label.head? ≠ some 255) : (Params.jsonl label).Lawful where
  link_binds p p' b b' h := by
    have h1 := hexOf_inj _ _ h
    exact jInput_inj (hcr _ _ h1)
  link_ne_genesis p b h := by
    have h1 := hexOf_inj _ _ h
    have h2 := hcr _ _ h1
    unfold jInput at h2
    by_cases hp : p.contains nl = true
    · simp only [hp, ite_true, jDirty] at h2
      apply hl2
      rw [← h2]; rfl
    · simp only [Bool.not_eq_true] at hp
      simp only [hp, Bool.false_eq_true, ite_false] at h2
      apply hl
      rw [← h2]; simp
  link_clean p b := hexOf_clean _
  dec_enc := jDec_jEnc
  enc_of_dec b e h := jEnc_jDec h
  enc_clean := jEnc_clean
  line_clean p e := jLine_clean _ (hexOf_clean _).1 e
  split_line p e := jSplit_jFrame _ (hexOf_no_quote _) e
  split_inv l d b h := jSplit_inv h
  sig_round i p b m := jSig_round ⟨i, jLink p b, m⟩ (hexOf_no_quote _)

end VbmJournal
