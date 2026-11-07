import VbmJournalProofs.Laws
/-! # The real parameters meet the laws, if SHA-256 is collision resistant

`Params.real` (`VbmJournal.Real`) is the chain the real driver writes: `link p b` is the hex of `sha256` of `chainInput p b`, and the genesis the
hex of the `sha256` of a label; the codec is the unary one. `real_lawful` says it meets `Params.Lawful`, so that every theorem of slice 1 and
slice 2 holds of it, **given that `sha256` is collision resistant** (`Sha256.CollisionFree`). That is a hypothesis about the shim: it is the
assumption A9 of docs/trust-boundary.md, a statement about a hash function no proof here can discharge (and, of an unbounded input, not literally true
of any function with 32 bytes of output: it is the cryptographic assumption that no one can find a collision). Nothing else is assumed of the C. -/
namespace VbmJournal

/-- **The assumption about the shim `sha256`**: two inputs with the same digest are the same input. -/
def Sha256.CollisionFree : Prop := ∀ a b : Bytes, sha256L a = sha256L b → a = b

theorem hexDigit_lt (n : Nat) (h : n < 16) : 48 ≤ (hexDigit n).toNat ∧ (hexDigit n).toNat ≤ 102 := by
  unfold hexDigit
  split <;> simp [Nat.toUInt8, UInt8.toNat_ofNat] <;> omega

theorem hexDigit_inj {a b : Nat} (ha : a < 16) (hb : b < 16) (h : hexDigit a = hexDigit b) : a = b := by
  unfold hexDigit at h
  have := congrArg UInt8.toNat h
  split at this <;> split at this <;> simp [Nat.toUInt8, UInt8.toNat_ofNat] at this <;> omega

theorem hexOf_inj : ∀ (a b : Bytes), hexOf a = hexOf b → a = b := by
  intro a
  induction a with
  | nil =>
    intro b h
    cases b with
    | nil => rfl
    | cons y ys => simp [hexOf] at h
  | cons x xs ih =>
    intro b h
    cases b with
    | nil => simp [hexOf] at h
    | cons y ys =>
      simp only [hexOf, List.flatMap_cons, List.cons_append, List.cons.injEq, List.nil_append] at h
      obtain ⟨h1, h2, h3⟩ := h
      have hx := x.toNat_lt
      have hy := y.toNat_lt
      have e1 := hexDigit_inj (by omega) (by omega) h1
      have e2 := hexDigit_inj (by omega) (by omega) h2
      have : x = y := by apply UInt8.toNat_inj.1; omega
      rw [this, ih ys (by simpa [hexOf] using h3)]

theorem hexOf_clean (b : Bytes) : nl ∉ hexOf b ∧ sp ∉ hexOf b := by
  have key : ∀ x ∈ hexOf b, 48 ≤ x.toNat := by
    intro x hx
    simp only [hexOf, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hx
    obtain ⟨y, _, hy⟩ := hx
    have hyl := y.toNat_lt
    rcases hy with rfl | rfl
    · exact (hexDigit_lt (y.toNat / 16) (by omega)).1
    · exact (hexDigit_lt (y.toNat % 16) (by omega)).1
  constructor
  · intro h; have := key _ h; simp [nl] at this
  · intro h; have := key _ h; simp [sp] at this

theorem chainInput_inj : ∀ (p p' b b' : Bytes), chainInput p b = chainInput p' b' → p = p' ∧ b = b' := by
  intro p
  induction p with
  | nil =>
    intro p' b b' h
    cases p' with
    | nil => simpa [chainInput] using h
    | cons x xs => simp [chainInput] at h
  | cons x xs ih =>
    intro p' b b' h
    cases p' with
    | nil => simp [chainInput] at h
    | cons y ys =>
      simp only [chainInput, List.flatMap_cons, List.cons_append, List.cons.injEq] at h
      obtain ⟨_, rfl, h2⟩ := h
      obtain ⟨h3, h4⟩ := ih ys b b' (by simpa [chainInput] using h2)
      subst h3
      exact ⟨rfl, h4⟩

/-- **The real parameters meet the laws of the chain and the codec**, if the shim `sha256` is collision resistant. -/
theorem real_lawful (hcr : Sha256.CollisionFree) : Params.real.Lawful where
  link_binds p p' b b' h := by
    have h1 := hexOf_inj _ _ h
    exact chainInput_inj _ _ _ _ (hcr _ _ h1)
  link_ne_genesis p b h := by
    have h1 := hexOf_inj _ _ h
    have h2 := hcr _ _ h1
    have : (chainInput p b).head? = (ascii "vbm-journal-v1").head? := by rw [h2]
    cases p with
    | nil => simp [chainInput, ascii] at this
    | cons x xs => simp [chainInput, ascii] at this
  link_clean p b := hexOf_clean _
  dec_enc := decUnary_encUnary
  enc_of_dec := encUnary_decUnary
  enc_clean := encUnary_clean

end VbmJournal
