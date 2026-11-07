import VbmJournalProofs.Chain
/-! # The compiled reader is the model: the flat buffer refines the list

The proofs read a journal as a `List UInt8`; the compiled code reads it as a `ByteArray`, by index, in a loop (`readB`, `verifyB`: `VbmJournal.Basic`),
so that a journal of megabytes costs a megabyte and not a list cell per byte. These are the theorems that the two agree:

* `readB_eq`: `readB P b = read P b.toList`, for every `Params`: the same entries, the same head, the same torn tail, or the same refusal.
* `recoverPlanB_eq`, `stepReplyB_eq`: the machine's step on the reply of a read, the bytes flat, is its step on the list.

The flat forms of the digest and of the codec (`Params.linkB`, `decB`) are fields of `Params` with their own proofs of agreement (`linkB_eq`, `decB_eq`),
so the refinement holds of whatever digest and codec the parameters carry. Nothing here is assumed. -/
namespace VbmJournal

/-! ## Finding a byte -/

theorem findByte_some (b : ByteArray) (x : UInt8) : ∀ i j, findByte b x i = some j →
    ∃ pre rest, b.toList.drop i = pre ++ x :: rest ∧ x ∉ pre ∧ j = i + pre.length ∧ rest = b.toList.drop (j + 1) := by
  intro i j h
  fun_induction findByte b x i generalizing j with
  | case1 i hi hx =>
    simp only [Option.some.injEq] at h
    subst h
    have hl : i < b.toList.length := by simpa using hi
    refine ⟨[], b.toList.drop (i + 1), ?_, by simp, by simp, rfl⟩
    rw [List.drop_eq_getElem_cons hl]
    simp only [List.nil_append, List.cons.injEq, and_true]
    simpa [toList_eq, ByteArray.getElem_eq_getElem_data] using hx
  | case2 i hi hx ih =>
    obtain ⟨pre, rest, h1, h2, h3, h4⟩ := ih j h
    have hl : i < b.toList.length := by simpa using hi
    refine ⟨b[i] :: pre, rest, ?_, ?_, ?_, h4⟩
    · rw [List.drop_eq_getElem_cons hl, h1]
      simp [toList_eq]
      exact (ByteArray.getElem_eq_getElem_data).symm
    · simp only [List.mem_cons, not_or]
      exact ⟨fun e => hx e.symm, h2⟩
    · simp; omega
  | case3 i hi => simp at h

theorem findByte_none (b : ByteArray) (x : UInt8) : ∀ i, findByte b x i = none → x ∉ b.toList.drop i := by
  intro i h
  fun_induction findByte b x i with
  | case1 i hi hx => simp at h
  | case2 i hi hx ih =>
    have hl : i < b.toList.length := by simpa using hi
    rw [List.drop_eq_getElem_cons hl]
    simp only [List.mem_cons, not_or]
    exact ⟨fun e => hx (by simpa [toList_eq, ByteArray.getElem_eq_getElem_data] using e.symm), ih h⟩
  | case3 i hi =>
    have : b.toList.drop i = [] := List.drop_eq_nil_of_le (by simp at hi ⊢; omega)
    simp [this]

theorem splitLine_none : ∀ (l : Bytes), sp ∉ l → splitLine l = none := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons b l ih =>
    intro h
    have hb : b ≠ sp := fun e => h (by simp [e])
    have hl : sp ∉ l := fun e => h (by simp [e])
    simp [splitLine, hb, ih hl]

theorem toList_extract_tail (b : ByteArray) (i : Nat) : (b.extract i b.size).toList = b.toList.drop i := by
  rw [toList_extract]
  apply List.take_of_length_le
  simp

/-- `splitLine` on a flat buffer is `splitLine` on its list. -/
theorem splitLineB_eq (l : ByteArray) :
    (splitLineB l).map (fun p => (p.1, p.2.toList)) = splitLine l.toList := by
  unfold splitLineB
  cases h : findByte l sp 0 with
  | none =>
    have := findByte_none l sp 0 h
    simp only [List.drop_zero] at this
    simp [splitLine_none _ this]
  | some i =>
    obtain ⟨pre, rest, h1, h2, h3, h4⟩ := findByte_some l sp 0 i h
    simp only [List.drop_zero] at h1
    have hs := splitLine_sealed rest h2
    rw [← h1] at hs
    have e1 : (l.extract 0 i).toList = pre := by
      rw [toList_extract, h1, h3]; simp
    have e2 : (l.extract (i + 1) l.size).toList = rest := by
      rw [toList_extract_tail, h4]
    simp [e1, e2, hs]

/-! ## Verifying -/

theorem verifyFrom_cons (P : Params) (prev : Digest) (l : Bytes) (ls : List Bytes) :
    verifyFrom P prev (l :: ls) =
      match splitLine l with
      | none => none
      | some (d, body) =>
        if P.link prev body = d then
          match P.dec body with
          | none => none
          | some e => (verifyFrom P d ls).map fun p => (e :: p.1, p.2)
        else none := rfl

/-- The loop of `verifyB` is `verifyFrom` over `parseLines`: entries (the new ones, reversed, before `acc`), head, and the index of the torn tail. -/
theorem verifyB_eq (P : Params) (b : ByteArray) : ∀ (n i : Nat) (prev : Digest) (acc : List Entry), b.size - i = n → i ≤ b.size →
    verifyB P b i prev acc =
      (verifyFrom P prev (parseLines (b.toList.drop i)).1).map
        (fun p => (p.1.reverse ++ acc, p.2, b.size - (parseLines (b.toList.drop i)).2.length)) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro i prev acc hn hi
    unfold verifyB
    split
    · rename_i hf
      have h0 := findByte_none b nl i hf
      have hl : (b.toList.drop i).length = b.size - i := by simp
      simp [parseLines_noNl h0, verifyFrom, hl]
      omega
    · rename_i j hf
      obtain ⟨pre, rest, h1, h2, h3, h4⟩ := findByte_some b nl i j hf
      have hjb := findByte_lt b nl i j hf
      have hpl : parseLines (b.toList.drop i) = (pre :: (parseLines rest).1, (parseLines rest).2) := by
        rw [h1]; exact parseLines_frame rest h2
      have hline : (b.extract i j).toList = pre := by
        rw [toList_extract, h1]
        have : j - i = pre.length := by omega
        rw [this]; simp
      have hrest : rest = b.toList.drop (j + 1) := h4
      have hih := ih (b.size - (j + 1)) (by omega) (j + 1) 
      rw [hpl, verifyFrom_cons]
      have hsp := splitLineB_eq (b.extract i j)
      rw [hline] at hsp
      cases hs : splitLineB (b.extract i j) with
      | none =>
        rw [hs] at hsp
        simp at hsp
        simp [← hsp]
      | some q =>
        obtain ⟨d, body⟩ := q
        rw [hs] at hsp
        simp only [Option.map_some] at hsp
        simp only [← hsp, P.linkB_eq, P.decB_eq]
        by_cases hlink : P.link prev body.toList = d
        · simp only [hlink, ite_true]
          cases hd : P.dec body.toList with
          | none => simp
          | some e =>
            simp only
            rw [hih d (e :: acc) rfl (by omega), ← hrest]
            cases hv : verifyFrom P d (parseLines rest).1 <;> simp [hrest]
        · simp [hlink]

/-- **`readB` is `read`**: the flat reader and the list reader return the same thing for the same bytes, whatever the parameters. -/
theorem readB_eq (P : Params) (b : ByteArray) : readB P b = read P b.toList := by
  unfold readB read
  rw [verifyB_eq P b _ 0 P.genesis [] rfl (Nat.zero_le _)]
  simp only [List.drop_zero]
  cases hv : verifyFrom P P.genesis (parseLines b.toList).1 with
  | none => simp
  | some p =>
    obtain ⟨es, h⟩ := p
    simp only [Option.map_some, List.append_nil, List.reverse_reverse]
    have htail : (b.extract (b.size - (parseLines b.toList).2.length) b.size).toList = (parseLines b.toList).2 := by
      rw [toList_extract_tail]
      have hs := (parseLines_spec b.toList _ _ rfl).1
      generalize (parseLines b.toList).1 = ls at hs ⊢
      generalize (parseLines b.toList).2 = t at hs ⊢
      have hlen : b.size - t.length = (flat ls).length := by
        have := congrArg List.length hs
        simp only [List.length_append, length_toList] at this
        omega
      rw [hlen, hs]
      simp
    rw [htail]

/-- **The machine's recovery on a flat buffer is its recovery on the list.** -/
theorem recoverPlanB_eq (P : Params) (st : St) (b : ByteArray) : recoverPlanB P st b = recoverPlan P st b.toList := by
  unfold recoverPlanB recoverPlan
  rw [readB_eq]
  cases read P b.toList with
  | none => rfl
  | some r =>
    have h0 : (b.toList = []) ↔ b.size = 0 := by
      rw [← List.length_eq_zero_iff, length_toList]
    simp only [h0, length_toList]

/-- **The reply of a read, the bytes flat, is the reply of the list**: one event of the model. -/
theorem stepReplyB_eq (P : Params) (st : St) (g : Nat) (b : ByteArray) :
    stepReplyB P st g b = step P st (.readReply g b.toList) := by
  unfold stepReplyB step
  by_cases hg : g = st.gen
  · simp only [hg, ite_true]
    cases st.mode <;> simp [recoverPlanB_eq]
  · simp [hg]

end VbmJournal
