import VbmJournalProofs.Chain
/-! # The signed head: what the signature file gives

`VbmJournal.verdict` is the verification of a journal against its signature file (`VbmJournal.Sig`), as lung's `LungSpec.JournalSig.verdict` is.
**Plain statements.**

* `sig_roundtrip`: what is signed is read back (the file `Sig.toBytes s` reads as `s`, when the head has no separator in it).
* `verdict_none`: no signature file, no signature: the journal is reported unsigned (an older journal).
* `verdict_signed`, `verdict_sound`: a journal is accepted as signed **only if** the file reads, the mac is the key's, the journal has at least the
  signed number of records, and the chain's head at that number is the signed head. The records after it are the unsigned tail (a crash between an
  append and its signature leaves some): reported, accepted.
* `verdict_unreadable`, `verdict_bad_mac`, `verdict_cut_back`, `verdict_rewritten`: it fails closed, each way with its own words.
* `verdict_anchored`, `signed_unique`: a journal accepted against a signature is **anchored** (`Anchored`, slice 1) at the signed point, so every journal
  accepted against the same signature has the same first `index` entries: the signature gives what the chain alone cannot (a journal cut back at its
  tail, which verifies, is refused: `verdict_cut_back`).
* `verdict_honest`: a signature made of a prefix of the journal (the writer's, whatever the crashes since) is accepted, with the rest as unsigned tail.

What is not proved: that HMAC-SHA256 is a message authentication code (the host's key makes `mac` unforgeable), and that the key is secret. Whoever
has the key can re-sign. -/
namespace VbmJournal

/-! ## Decimal numbers -/

theorem natDec_eq (n : Nat) : natDec n = if n < 10 then [(48 + n).toUInt8] else natDec (n / 10) ++ [(48 + n % 10).toUInt8] := by
  rw [natDec]

theorem natDec_digits (n : Nat) : ∀ d ∈ natDec n, 48 ≤ d.toNat ∧ d.toNat ≤ 57 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro d hd
    rw [natDec_eq] at hd
    split at hd
    · simp at hd; subst hd; simp [UInt8.toNat_ofNat]; omega
    · simp only [List.mem_append, List.mem_singleton] at hd
      rcases hd with hd | rfl
      · exact ih (n / 10) (by omega) d hd
      · simp [Nat.toUInt8, UInt8.toNat_ofNat]; omega

theorem natDec_ne_nil (n : Nat) : natDec n ≠ [] := by
  rw [natDec_eq]
  split
  · simp
  · simp

theorem foldl_natDec (n : Nat) : (natDec n).foldl (fun a d => a * 10 + (d.toNat - 48)) 0 = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [natDec_eq]
    split
    · rename_i h
      simp [UInt8.toNat_ofNat]; omega
    · rename_i h
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, ih (n / 10) (by omega)]
      simp [Nat.toUInt8, UInt8.toNat_ofNat]
      omega

/-- A number in decimal is read back. -/
theorem parseDec_natDec (n : Nat) : parseDec (natDec n) = some n := by
  unfold parseDec
  have h1 : (!(natDec n).isEmpty && (natDec n).all fun d => decide (48 ≤ d.toNat) && decide (d.toNat ≤ 57)) = true := by
    have : (natDec n).isEmpty = false := by
      cases h : natDec n with
      | nil => exact absurd h (natDec_ne_nil n)
      | cons => rfl
    simp only [this, Bool.not_false, Bool.true_and, List.all_eq_true]
    intro d hd
    have := natDec_digits n d hd
    simp [this.1, this.2]
  simp [h1, foldl_natDec]

/-- No separator in a decimal number. -/
theorem sp_not_natDec (n : Nat) : sp ∉ natDec n := by
  intro h
  have := natDec_digits n sp h
  simp [sp] at this

/-! ## The file -/

theorem splitLine_cons_sp (a r : Bytes) (h : sp ∉ a) : splitLine (a ++ sp :: r) = some (a, r) := by
  induction a with
  | nil => simp [splitLine]
  | cons b a ih =>
    have hb : b ≠ sp := fun e => h (by simp [e])
    have ha : sp ∉ a := fun e => h (by simp [e])
    simp [splitLine, hb, ih ha]

/-- **What is signed is read back.** -/
theorem sig_roundtrip (s : Sig) (h : sp ∉ s.head) : Sig.ofBytes s.toBytes = some s := by
  obtain ⟨i, hd, m⟩ := s
  simp only at h
  simp [Sig.toBytes, Sig.ofBytes, splitLine_cons_sp _ _ (sp_not_natDec i), splitLine_cons_sp _ _ h, parseDec_natDec]

/-! ## The verdict -/

variable {P : Params} {mac : Nat → Digest → Bytes} {es : List Entry}

theorem verdict_none : verdict P mac es none = .ok .unsigned := rfl

theorem verdict_unreadable {t : Bytes} (h : Sig.ofBytes t = none) : verdict P mac es (some t) = .error unreadableMsg := by
  simp [verdict, h]

theorem verdict_bad_mac {t : Bytes} {s : Sig} (hp : Sig.ofBytes t = some s) (hm : mac s.index s.head ≠ s.mac) :
    verdict P mac es (some t) = .error macMsg := by
  simp [verdict, hp, hm]

theorem verdict_cut_back {t : Bytes} {s : Sig} (hp : Sig.ofBytes t = some s) (hm : mac s.index s.head = s.mac) (hc : es.length < s.index) :
    verdict P mac es (some t) = .error (cutMsg es.length s.index) := by
  simp [verdict, hp, hm, hc]

theorem verdict_rewritten {t : Bytes} {s : Sig} (hp : Sig.ofBytes t = some s) (hm : mac s.index s.head = s.mac) (hc : s.index ≤ es.length)
    (hr : headFrom P P.genesis (es.take s.index) ≠ s.head) : verdict P mac es (some t) = .error (rewrittenMsg s.index) := by
  have : ¬ es.length < s.index := by omega
  simp [verdict, hp, hm, this, hr]

/-- **A valid signature is accepted, and the records after it are the unsigned tail.** -/
theorem verdict_signed {t : Bytes} {s : Sig} (hp : Sig.ofBytes t = some s) (hm : mac s.index s.head = s.mac) (hc : s.index ≤ es.length)
    (hr : headFrom P P.genesis (es.take s.index) = s.head) :
    verdict P mac es (some t) = .ok (.signed s.index (es.length - s.index)) := by
  have : ¬ es.length < s.index := by omega
  simp [verdict, hp, hm, this, hr]

/-- **Fail closed: a journal is accepted as signed only if the file reads, the mac is the key's, the journal was not cut back and the chain's head
at the signed index is the signed head.** -/
theorem verdict_sound {t : Bytes} {i k : Nat} (hv : verdict P mac es (some t) = .ok (.signed i k)) :
    ∃ s, Sig.ofBytes t = some s ∧ mac s.index s.head = s.mac ∧ s.index ≤ es.length ∧
      headFrom P P.genesis (es.take s.index) = s.head ∧ i = s.index ∧ k = es.length - s.index := by
  cases hp : Sig.ofBytes t with
  | none => simp [verdict, hp] at hv
  | some s =>
    refine ⟨s, rfl, ?_⟩
    simp only [verdict, hp] at hv
    split at hv
    · simp at hv
    · rename_i h1
      split at hv
      · simp at hv
      · rename_i h2
        split at hv
        · simp at hv
        · rename_i h3
          simp only [Except.ok.injEq, Verdict.signed.injEq] at hv
          obtain ⟨rfl, rfl⟩ := hv
          exact ⟨by simpa using h1, by omega, by simpa using h3, rfl, rfl⟩

/-- An unsigned verdict is only given to a journal with no signature file. -/
theorem verdict_unsigned_only {o : Option Bytes} (hv : verdict P mac es o = .ok .unsigned) : o = none := by
  cases o with
  | none => rfl
  | some t =>
    cases hp : Sig.ofBytes t with
    | none => simp [verdict, hp] at hv
    | some s =>
      simp only [verdict, hp] at hv
      split at hv
      · simp at hv
      · split at hv
        · simp at hv
        · split at hv <;> simp at hv

/-- **A signature that the writer made of a prefix of the journal is accepted**, whatever happened to the journal after it (appends, a torn tail,
recovery): the records after it are the unsigned tail. -/
theorem verdict_honest {i : Nat} (hi : i ≤ es.length) (hsp : sp ∉ headFrom P P.genesis (es.take i)) :
    verdict P mac es (some (Sig.make mac i (headFrom P P.genesis (es.take i))).toBytes) = .ok (.signed i (es.length - i)) := by
  have hr := sig_roundtrip (Sig.make mac i (headFrom P P.genesis (es.take i))) hsp
  exact verdict_signed hr rfl hi rfl

/-- **An accepted signature anchors the journal** at the signed point (slice 1's `Anchored`). -/
theorem verdict_anchored {b : Bytes} {r : Read} (hr : read P b = some r) {t : Bytes} {i k : Nat}
    (hv : verdict P mac r.entries (some t) = .ok (.signed i k)) (s : Sig) (hs : Sig.ofBytes t = some s) :
    Anchored P i s.head b := by
  obtain ⟨s', hs', _, hle, hh, hi, _⟩ := verdict_sound hv
  rw [hs] at hs'
  cases hs'
  exact ⟨r, hr, by omega, by rw [hi]; exact hh⟩

section Lawful
variable (L : P.Lawful)
include L

/-- **The signature fixes the journal's first records**: two journals (as read) accepted against the same signature file have the same first `index`
entries. A journal cut back, or rewritten, before the signed point is refused (above); one rewritten after it is the unsigned tail. -/
theorem signed_unique {ra rb : Read} {t : Bytes} {i k k' : Nat}
    (hva : verdict P mac ra.entries (some t) = .ok (.signed i k)) (hvb : verdict P mac rb.entries (some t) = .ok (.signed i k')) :
    ra.entries.take i = rb.entries.take i := by
  obtain ⟨s, hs, _, hle, hh, hi, _⟩ := verdict_sound hva
  obtain ⟨s2, hs2, _, hle2, hh2, hi2, _⟩ := verdict_sound hvb
  rw [hs] at hs2
  cases hs2
  have := headFrom_inj L _ _ (hh.trans hh2.symm)
  rw [hi]; exact this

end Lawful

end VbmJournal
