import VbmJournalProofs.Sig
/-! # The plain-text line and signature file meet the format laws

The line `digest ' ' body` and the signature file `index head mac` (slices 1 and 2, `Params.ofLists`) meet the format laws of `Params.Lawful` (`line_clean`, `split_line`,
`split_inv`, `sig_round`) when a digest has no newline and no separator in it and an encoded entry no newline: what `link_clean` and `enc_clean` say. -/
namespace VbmJournal

theorem space_split_inv (l d b : Bytes) (h : splitSp l = some (d, b)) : l = d ++ sp :: b := (splitSp_inv l d b h).1

/-- The four format laws of the plain-text line and signature file, from the cleanliness of digests and entries. -/
theorem space_laws (P : Params) (hf : ∀ d b, P.frameLine d b = d ++ sp :: b) (hs : P.splitLine = splitSp)
    (hse : P.sigEnc = Sig.toBytes) (hsd : P.sigDec = Sig.ofBytes)
    (hlc : ∀ p b, nl ∉ P.link p b ∧ sp ∉ P.link p b) (hec : ∀ e, nl ∉ P.enc e) :
    (∀ p e, nl ∉ P.frameLine (P.link p (P.enc e)) (P.enc e)) ∧
    (∀ p e, P.splitLine (P.frameLine (P.link p (P.enc e)) (P.enc e)) = some (P.link p (P.enc e), P.enc e)) ∧
    (∀ l d b, P.splitLine l = some (d, b) → l = P.frameLine d b) ∧
    (∀ i p b m, P.sigDec (P.sigEnc ⟨i, P.link p b, m⟩) = some ⟨i, P.link p b, m⟩) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p e
    rw [hf]
    simp only [List.mem_append, List.mem_cons, not_or]
    exact ⟨(hlc _ _).1, by decide, hec e⟩
  · intro p e
    rw [hf, hs]
    exact splitSp_sealed _ (hlc _ _).2
  · intro l d b h
    rw [hf]
    rw [hs] at h
    exact space_split_inv l d b h
  · intro i p b m
    rw [hse, hsd]
    exact sig_roundtrip ⟨i, P.link p b, m⟩ (hlc p b).2

end VbmJournal
