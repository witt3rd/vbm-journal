import VbmJournal
/-! # What the proofs need of the two parameters

The model (`VbmJournal.Basic`) leaves the digest and the codec open. These are the laws the theorems assume of them, stated once.
`Params.Lawful` is a hypothesis of the theorems, never an axiom: the codec laws are proved for the concrete codec below
(`decUnary_encUnary`, `encUnary_decUnary`, `encUnary_clean`), and all the laws are met by a symbolic digest with that codec
(`sym_lawful`, in `Witness`), so the hypothesis is not vacuous.
That SHA-256 satisfies the digest laws is collision resistance, an assumption about the shim (docs/trust-boundary.md A9), not a theorem. -/
namespace VbmJournal

/-- The laws of the digest chain and of the codec. -/
structure Params.Lawful (P : Params) : Prop where
  /-- **The digest binds**: a digest determines the digest before it and the body (collision resistance). -/
  link_binds : ∀ p p' b b', P.link p b = P.link p' b' → p = p' ∧ b = b'
  /-- No digest of a line is the genesis digest. -/
  link_ne_genesis : ∀ p b, P.link p b ≠ P.genesis
  /-- A digest has neither a newline nor a separator in it (it is hex). -/
  link_clean : ∀ p b, nl ∉ P.link p b ∧ sp ∉ P.link p b
  /-- The codec round-trips. -/
  dec_enc : ∀ e, P.dec (P.enc e) = some e
  /-- The codec is canonical: what decodes is what encoding gives back. -/
  enc_of_dec : ∀ b e, P.dec b = some e → P.enc e = b
  /-- An encoded entry has no newline. -/
  enc_clean : ∀ e, nl ∉ P.enc e

namespace Params.Lawful
variable {P : Params} (L : P.Lawful)
include L

theorem enc_inj {e e' : Entry} (h : P.enc e = P.enc e') : e = e' := by
  have := L.dec_enc e
  rw [h, L.dec_enc e'] at this
  exact (Option.some.inj this).symm

end Params.Lawful

/-! ## The concrete codec satisfies the codec laws -/

private theorem all_replicate {r : Bytes} (h : (r.all fun x => x == 49) = true) : r = List.replicate r.length 49 := by
  induction r with
  | nil => rfl
  | cons a t ih =>
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    simp only [List.length_cons, List.replicate_succ]
    rw [h.1, ← ih h.2]

theorem decUnary_encUnary (e : Entry) : decUnary (encUnary e) = some e := by
  cases e with
  | note n => simp [encUnary, decUnary]
  | call i => simp [encUnary, decUnary]
  | done i b => cases b <;> simp [encUnary, decUnary]

theorem encUnary_decUnary (b : Bytes) (e : Entry) (h : decUnary b = some e) : encUnary e = b := by
  unfold decUnary at h
  split at h
  · rename_i r
    split at h
    · rename_i ha; cases h; simp [encUnary]; exact (all_replicate ha).symm
    · simp at h
  · rename_i r
    split at h
    · rename_i ha; cases h; simp [encUnary]; exact (all_replicate ha).symm
    · simp at h
  · rename_i r
    split at h
    · rename_i ha; cases h; simp [encUnary]; exact (all_replicate ha).symm
    · simp at h
  · rename_i r
    split at h
    · rename_i ha; cases h; simp [encUnary]; exact (all_replicate ha).symm
    · simp at h
  · simp at h

theorem encUnary_clean (e : Entry) : nl ∉ encUnary e := by
  cases e with
  | note n => simp [encUnary, nl]
  | call i => simp [encUnary, nl]
  | done i b => cases b <;> simp [encUnary, nl]

end VbmJournal
