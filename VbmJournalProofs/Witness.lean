import VbmJournalProofs.Laws
/-! # The laws are satisfiable

`Params.Lawful` is a hypothesis of the theorems; here is a `Params` that meets it, so the hypothesis is not empty. The digest is
symbolic: `link p b` writes `p` and `b` out in full, in a unary code with delimiters, so it binds by construction (it is not a hash:
it is as long as its input). The codec is the concrete unary one. SHA-256 meets the same laws up to collision resistance, which is
the assumption about the slice-2 shim (docs/trust-boundary.md A9). -/
namespace VbmJournal

/-- A byte, in unary: `a` repeated, then `b`. -/
def sym1 (x : UInt8) : Bytes := List.replicate x.toNat 97 ++ [98]

/-- A byte string, written out. -/
def symB (l : Bytes) : Bytes := l.flatMap sym1

/-- The symbolic digest: `c`, the previous digest, `d`, the body. -/
def symLink (p b : Bytes) : Bytes := 99 :: (symB p ++ 100 :: symB b)

/-- The symbolic parameters. -/
def Params.sym : Params where
  genesis := [101]
  link := symLink
  enc := encUnary
  dec := decUnary

private theorem rep_inj : ∀ (n m : Nat) (r r' : Bytes),
    List.replicate n (97 : UInt8) ++ 98 :: r = List.replicate m 97 ++ 98 :: r' → n = m ∧ r = r' := by
  intro n
  induction n with
  | zero =>
    intro m r r' h
    cases m with
    | zero => simpa using h
    | succ m => simp [List.replicate_succ] at h
  | succ n ih =>
    intro m r r' h
    cases m with
    | zero => simp [List.replicate_succ] at h
    | succ m =>
      simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
      have := ih m r r' h
      exact ⟨by omega, this.2⟩

private theorem sym1_inj {x y : UInt8} {r r' : Bytes} (h : sym1 x ++ r = sym1 y ++ r') : x = y ∧ r = r' := by
  simp only [sym1, List.append_assoc, List.singleton_append] at h
  obtain ⟨h1, h2⟩ := rep_inj _ _ _ _ h
  exact ⟨UInt8.toNat_inj.1 h1, h2⟩

private theorem sym1_first (x : UInt8) (r : Bytes) : ∃ t, sym1 x ++ r = 97 :: t ∨ sym1 x ++ r = 98 :: t := by
  cases hn : x.toNat with
  | zero => exact ⟨r, Or.inr (by simp [sym1, hn])⟩
  | succ n => exact ⟨List.replicate n 97 ++ 98 :: r, Or.inl (by simp [sym1, hn, List.replicate_succ])⟩

private theorem symB_inj : ∀ (b b' : Bytes), symB b = symB b' → b = b' := by
  intro b
  induction b with
  | nil =>
    intro b' h
    cases b' with
    | nil => rfl
    | cons y l' =>
      exfalso
      simp only [symB, List.flatMap_nil, List.flatMap_cons] at h
      obtain ⟨t, ht⟩ := sym1_first y (l'.flatMap sym1)
      rcases ht with ht | ht <;> rw [ht] at h <;> simp at h
  | cons x l ih =>
    intro b' h
    cases b' with
    | nil =>
      exfalso
      simp only [symB, List.flatMap_nil, List.flatMap_cons] at h
      obtain ⟨t, ht⟩ := sym1_first x (l.flatMap sym1)
      rcases ht with ht | ht <;> rw [ht] at h <;> simp at h
    | cons y l' =>
      simp only [symB, List.flatMap_cons] at h
      obtain ⟨h1, h2⟩ := sym1_inj h
      rw [h1, ih l' h2]

private theorem symB_inj_delim : ∀ (p p' b b' : Bytes), symB p ++ 100 :: symB b = symB p' ++ 100 :: symB b' → p = p' ∧ b = b' := by
  intro p
  induction p with
  | nil =>
    intro p' b b' h
    cases p' with
    | nil =>
      simp only [symB, List.flatMap_nil, List.nil_append, List.cons.injEq, true_and] at h
      exact ⟨rfl, symB_inj _ _ h⟩
    | cons y p' =>
      exfalso
      simp only [symB, List.flatMap_nil, List.nil_append, List.flatMap_cons] at h
      obtain ⟨t, ht⟩ := sym1_first y (p'.flatMap sym1 ++ 100 :: b'.flatMap sym1)
      rcases ht with ht | ht <;> rw [List.append_assoc, ht] at h <;> simp at h
  | cons x p ih =>
    intro p' b b' h
    cases p' with
    | nil =>
      exfalso
      simp only [symB, List.flatMap_nil, List.nil_append, List.flatMap_cons] at h
      obtain ⟨t, ht⟩ := sym1_first x (p.flatMap sym1 ++ 100 :: b.flatMap sym1)
      rcases ht with ht | ht <;> rw [List.append_assoc, ht] at h <;> simp at h
    | cons y p' =>
      simp only [symB, List.flatMap_cons, List.append_assoc] at h
      obtain ⟨h1, h2⟩ := sym1_inj h
      obtain ⟨h3, h4⟩ := ih p' b b' h2
      subst h1; subst h3; subst h4
      exact ⟨rfl, rfl⟩

private theorem symB_mem (l : Bytes) : ∀ a ∈ symB l, a = 97 ∨ a = 98 := by
  induction l with
  | nil => simp [symB]
  | cons x l ih =>
    intro a ha
    simp only [symB, List.flatMap_cons, List.mem_append, sym1] at ha
    rcases ha with (ha | ha) | ha
    · simp [List.mem_replicate] at ha; exact Or.inl ha.2
    · simp at ha; exact Or.inr ha
    · exact ih a ha

/-- The parameters meet every law: the hypothesis `Params.Lawful` of the theorems is satisfiable. -/
theorem sym_lawful : Params.sym.Lawful where
  link_binds p p' b b' h := by
    simp only [Params.sym, symLink, List.cons.injEq, true_and] at h
    exact symB_inj_delim _ _ _ _ h
  link_ne_genesis p b h := by simp [Params.sym, symLink] at h
  link_clean p b := by
    have hall : ∀ a ∈ Params.sym.link p b, a = 99 ∨ a = 97 ∨ a = 98 ∨ a = 100 := by
      intro a ha
      simp only [Params.sym, symLink, List.mem_cons, List.mem_append] at ha
      rcases ha with ha | ha | ha | ha
      · exact Or.inl ha
      · rcases symB_mem p a ha with h | h <;> simp [h]
      · exact Or.inr (Or.inr (Or.inr ha))
      · rcases symB_mem b a ha with h | h <;> simp [h]
    constructor
    · intro h; have := hall _ h; simp [nl] at this
    · intro h; have := hall _ h; simp [sp] at this
  dec_enc := decUnary_encUnary
  enc_of_dec := encUnary_decUnary
  enc_clean := encUnary_clean

end VbmJournal
