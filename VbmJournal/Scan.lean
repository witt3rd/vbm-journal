import VbmJournal.Bytes
import VbmJournal.Format
/-! # vbm-journal slice 3, part 3: scanning a flat buffer

Finding a byte in a `ByteArray` by index (a loop), and cutting a plain-text line at its separator on a flat buffer: `splitSpB` is `splitSp` on the buffer's
list (`splitSpB_eq`). What the flat reader (`VbmJournal.Basic.readB`) and the flat forms of the formats are made of. `Init` only. -/
namespace VbmJournal

/-- The index of the first byte `x` at or after `i`. -/
def findByte (b : ByteArray) (x : UInt8) (i : Nat) : Option Nat :=
  if h : i < b.size then
    if b[i]'h = x then some i else findByte b x (i + 1)
  else none
termination_by b.size - i

theorem findByte_lt (b : ByteArray) (x : UInt8) (i j : Nat) (h : findByte b x i = some j) : i ≤ j ∧ j < b.size := by
  fun_induction findByte b x i with
  | case1 i hi hx => simp at h; omega
  | case2 i hi hx ih => have := ih h; omega
  | case3 i hi => simp at h


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

/-- `splitSp` on a flat buffer: the digest (a list: a few dozen bytes) and the body (flat). -/
def splitSpB (l : ByteArray) : Option (Digest × ByteArray) :=
  match findByte l sp 0 with
  | none => none
  | some i => some ((l.extract 0 i).toList, l.extract (i + 1) l.size)


theorem splitSp_sealed {d : Digest} (body : Bytes) (h : sp ∉ d) : splitSp (d ++ sp :: body) = some (d, body) := by
  induction d with
  | nil => simp [splitSp]
  | cons b d ih =>
    have hb : b ≠ sp := fun e => h (by simp [e])
    have hd : sp ∉ d := fun e => h (by simp [e])
    simp [splitSp, hb, ih hd]

theorem splitSp_none : ∀ (l : Bytes), sp ∉ l → splitSp l = none := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons b l ih =>
    intro h
    have hb : b ≠ sp := fun e => h (by simp [e])
    have hl : sp ∉ l := fun e => h (by simp [e])
    simp [splitSp, hb, ih hl]

theorem toList_extract_tail (b : ByteArray) (i : Nat) : (b.extract i b.size).toList = b.toList.drop i := by
  rw [toList_extract]
  apply List.take_of_length_le
  simp

/-- `splitSp` on a flat buffer is `splitSp` on its list. -/
theorem splitSpB_eq (l : ByteArray) :
    (splitSpB l).map (fun p => (p.1, p.2.toList)) = splitSp l.toList := by
  unfold splitSpB
  cases h : findByte l sp 0 with
  | none =>
    have := findByte_none l sp 0 h
    simp only [List.drop_zero] at this
    simp [splitSp_none _ this]
  | some i =>
    obtain ⟨pre, rest, h1, h2, h3, h4⟩ := findByte_some l sp 0 i h
    simp only [List.drop_zero] at h1
    have hs := splitSp_sealed rest h2
    rw [← h1] at hs
    have e1 : (l.extract 0 i).toList = pre := by
      rw [toList_extract, h1, h3]; simp
    have e2 : (l.extract (i + 1) l.size).toList = rest := by
      rw [toList_extract_tail, h4]
    simp [e1, e2, hs]

end VbmJournal
