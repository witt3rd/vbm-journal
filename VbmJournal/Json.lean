import VbmJournal.Real
/-! # vbm-journal slice 3, part 4: the JSON-lines journal

The format of a host that keeps its journal as **JSON lines with a digest chain**, and can keep it: a line is one compact JSON object whose first key is the
digest, `{"c":"<hex>",<the rest of the record>}`; the digest of a record is the hex of `SHA-256(prev "\n" body)`, where `prev` is the digest of the record before
(the hex text, then a newline) and `body` is the record's compact JSON **without** the `c` key: the line with `"c":"<hex>",` cut out. A signature file is the
compact JSON object `{"head":"<hex>","index":<n>,"mac":"<hex>"}`. This is what `Params.jsonl label` writes and reads, byte for byte, and the library never parses
JSON: it cuts the digest out of the line by position.

* **The record** is `Entry.body` (a host record is its JSON text, `Body`), and the host maps its own records onto it. The library's own entries (`note`, `call`, `done`) are
  written in the same format as `{"vbm":"<unary code>"}`, so that every `Entry` has a line; a body must not begin with the key `vbm` (`bodyWf`).
* **The genesis** is the hex of `SHA-256(label)`; the label is the host's (a parameter: the library names no host).
* **The chain input** is `prev "\n" body`. A digest with a newline in it never occurs (digests are hex), but `link` is defined for every input and must bind for every
  input (`Params.Lawful.link_binds`): such a `prev` is hashed in a different encoding, one that has no newline (`jDirty`), so no two inputs share a hash input.
* **What it reads is what it writes**: a line is accepted only in exactly the form the writer makes (digest first, no whitespace). A journal whose lines are valid JSON
  but written otherwise is refused (fail closed), not reinterpreted.

The flat forms (`linkB`, `decB`, `splitB`) work on the `ByteArray` of the file, and are proved equal to the list forms (the fields `linkB_eq`, `decB_eq`, `splitB_eq`). `Init` only. -/
namespace VbmJournal

/-! ## The bytes of the format -/

/-- `{"c":"`: a line begins with its digest. -/
def jPre : Bytes := [123, 34, 99, 34, 58, 34]
/-- `",`: the digest ends, the record's other keys follow. -/
def jMid : Bytes := [34, 44]
/-- `{"vbm":"`: the library's own entries. -/
def jVbm : Bytes := [123, 34, 118, 98, 109, 34, 58, 34]
/-- `"}`. -/
def jEnd : Bytes := [34, 125]

/-- Do the bytes begin with `p`? -/
def startsL (p l : Bytes) : Bool := l.take p.length == p

/-- Do the flat bytes begin with `p`? Only the few bytes of `p` become a list. -/
def startsB (l : ByteArray) (p : Bytes) : Bool := (l.extract 0 p.length).toList == p

theorem startsB_eq (l : ByteArray) (p : Bytes) : startsB l p = startsL p l.toList := by
  simp [startsB, startsL, toList_extract]

/-! ## The line -/

/-- The line of a digest and a body (`{"` …): the digest first, then the body with its opening brace taken away. -/
def jFrame (d b : Bytes) : Bytes := jPre ++ d ++ jMid ++ b.drop 1

/-- Cut a line, after `{"c":"`, into its digest (up to the quote) and its body (`{`, and what follows `",`). -/
def jCut : Bytes → Option (Digest × Bytes)
  | [] => none
  | b :: r =>
    if b = 34 then (match r with | 44 :: t => some ([], 123 :: t) | _ => none)
    else (jCut r).map fun p => (b :: p.1, p.2)

/-- Cut a line into its digest and its body. -/
def jSplit (l : Bytes) : Option (Digest × Bytes) :=
  if startsL jPre l then jCut (l.drop 6) else none

/-- The line on a flat buffer. -/
def jSplitB (l : ByteArray) : Option (Digest × ByteArray) :=
  if startsB l jPre then
    match findByte l 34 6 with
    | none => none
    | some i =>
      if h : i + 1 < l.size then
        if l[i + 1]'h = 44 then some ((l.extract 6 i).toList, ByteArray.mk #[123] ++ l.extract (i + 2) l.size) else none
      else none
  else none

theorem jCut_none : ∀ (r : Bytes), 34 ∉ r → jCut r = none := by
  intro r
  induction r with
  | nil => intro _; rfl
  | cons b r ih =>
    intro h
    have hb : b ≠ 34 := fun e => h (by simp [e])
    have hr : 34 ∉ r := fun e => h (by simp [e])
    simp [jCut, hb, ih hr]

theorem jCut_find (rest : Bytes) : ∀ (pre : Bytes), 34 ∉ pre →
    jCut (pre ++ 34 :: rest) = (match rest with | 44 :: t => some (pre, 123 :: t) | _ => none) := by
  intro pre
  induction pre with
  | nil => intro _; simp [jCut]; rfl
  | cons b pre ih =>
    intro h
    have hb : b ≠ 34 := fun e => h (by simp [e])
    have hr : 34 ∉ pre := fun e => h (by simp [e])
    have hj : jCut (b :: (pre ++ 34 :: rest)) = (jCut (pre ++ 34 :: rest)).map fun p => (b :: p.1, p.2) := by
      simp [jCut, hb]
    rw [List.cons_append, hj, ih hr]
    rcases rest with _ | ⟨x, xs⟩
    · rfl
    · by_cases hx : x = 44
      · subst hx; rfl
      · simp [hx]

theorem jSplitB_eq (l : ByteArray) : (jSplitB l).map (fun q => (q.1, q.2.toList)) = jSplit l.toList := by
  unfold jSplitB jSplit
  rw [startsB_eq]
  by_cases hp : startsL jPre l.toList = true
  · simp only [hp, ite_true]
    cases hf : findByte l 34 6 with
    | none =>
      have := findByte_none l 34 6 hf
      simp [jCut_none _ this]
    | some i =>
      obtain ⟨pre, rest, h1, h2, h3, h4⟩ := findByte_some l 34 6 i hf
      rw [h1, jCut_find rest pre h2]
      have e1 : (l.extract 6 i).toList = pre := by
        rw [toList_extract, h1, h3]; simp
      by_cases hi : i + 1 < l.size
      · have hl : i + 1 < l.toList.length := by simpa using hi
        have hr : rest = l[i + 1] :: l.toList.drop (i + 2) := by
          rw [h4, List.drop_eq_getElem_cons hl]; simp [toList_eq, ByteArray.getElem_eq_getElem_data]
        simp only [hi, dite_true]
        rw [hr]
        by_cases h44 : l[i + 1] = 44
        · have e2 : (ByteArray.mk #[123] ++ l.extract (i + 2) l.size).toList = 123 :: l.toList.drop (i + 2) := by
            rw [toList_append, toList_extract_tail]; simp [toList_eq]
          simp [h44, e1, e2]
        · simp [h44]
      · have hr : rest = [] := by
          rw [h4]; exact List.drop_eq_nil_of_le (by simp; omega)
        simp [hi, hr]
  · simp [hp]

/-! ## The record -/

/-- The text of `s` after dropping a suffix `s`. -/
def stripSuf (s l : Bytes) : Option Bytes :=
  if s.length ≤ l.length && l.drop (l.length - s.length) == s then some (l.take (l.length - s.length)) else none

/-- The library's own entries are never a host record. -/
def jLib (m : Bytes) : Option Entry :=
  match decUnary m with
  | some (.body _) => none
  | r => r

/-- A record as written: the host's text as it is, a library entry as `{"vbm":"<unary code>"}`. -/
def jEnc : Entry → Bytes
  | .body b => b.bytes.toList
  | e => jVbm ++ encUnary e ++ jEnd

/-- A record read: a library entry, a host record, or nothing. -/
def jDec (l : Bytes) : Option Entry :=
  if startsL jVbm l then (stripSuf jEnd (l.drop 8)).bind jLib
  else if h : bodyWf l = true then some (.body ⟨l.toByteArray, by simpa using h⟩) else none

/-- `bodyWf` on a flat buffer. -/
def bodyWfB (b : ByteArray) : Bool :=
  startsB b [123, 34] && !startsB b [123, 34, 118, 98, 109, 34] && (findByte b nl 0).isNone

theorem bodyWfB_eq (b : ByteArray) : bodyWfB b = bodyWf b.toList := by
  unfold bodyWfB bodyWf
  rw [startsB_eq, startsB_eq]
  simp only [startsL, List.length_cons, List.length_nil]
  congr 1
  cases h : findByte b nl 0 with
  | none =>
    have := findByte_none b nl 0 h
    simp only [List.drop_zero] at this
    simp [this]
  | some i =>
    obtain ⟨pre, rest, h1, _⟩ := findByte_some b nl 0 i h
    simp only [List.drop_zero] at h1
    simp [h1]

/-- A record on a flat buffer: a host record is kept as it is, never copied into a list. -/
def jDecB (b : ByteArray) : Option Entry :=
  if startsB b jVbm then
    if 10 ≤ b.size && (b.extract (b.size - 2) b.size).toList == jEnd then jLib (b.extract 8 (b.size - 2)).toList else none
  else if h : bodyWfB b = true then some (.body ⟨b, by rw [← bodyWfB_eq]; exact h⟩) else none

theorem jDecB_eq (b : ByteArray) : jDecB b = jDec b.toList := by
  unfold jDecB jDec
  rw [startsB_eq]
  by_cases hv : startsL jVbm b.toList = true
  · simp only [hv, ite_true]
    have hl : (b.toList.drop 8).length = b.size - 8 := by simp
    unfold stripSuf
    rw [hl]
    by_cases h10 : 10 ≤ b.size
    · have e1 : (b.extract (b.size - 2) b.size).toList = b.toList.drop (b.size - 2) := toList_extract_tail b _
      have e3 : (b.extract 8 (b.size - 2)).toList = (b.toList.drop 8).take (b.size - 8 - jEnd.length) := by
        rw [toList_extract]; simp [jEnd]; congr 1; omega
      simp only [e1, e3, jEnd, List.length_cons, List.length_nil, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
      have : (10 ≤ b.size) = (2 ≤ b.size - 8) := by simp; omega
      have e4 : 8 + (b.size - 8 - 2) = b.size - 2 := by omega
      simp [h10, show 2 ≤ b.size - 8 by omega, e4]
      split <;> simp
    · have : ¬ (2 ≤ b.size - 8) := by omega
      simp [h10, this, jEnd]
  · simp only [hv, Bool.false_eq_true, ite_false]
    by_cases hw : bodyWf b.toList = true
    · have hw' : bodyWfB b = true := by rw [bodyWfB_eq]; exact hw
      simp only [hw, hw', dite_true]
      simp
    · have hw' : ¬ bodyWfB b = true := by rw [bodyWfB_eq]; exact hw
      simp [hw, hw']

/-! ## The digest -/

/-- The hash input of a link whose previous digest has a newline in it (never a digest of a journal: they are hex): no newline anywhere, a first byte no label has, so
it is never the input of a link whose previous digest is clean. -/
def jDirty (p b : Bytes) : Bytes := 255 :: hexOf (chainInput p b)

/-- The hash input of a link: `prev "\n" body`. -/
def jInput (p b : Bytes) : Bytes := if p.contains nl then jDirty p b else p ++ nl :: b

/-- The digest of a record after the digest `p`: the hex of `SHA-256(p "\n" b)`. -/
def jLink (p b : Bytes) : Digest := hexOf (sha256L (jInput p b))

/-- The hash input on a flat body. -/
def jInputB (p : Bytes) (b : ByteArray) : ByteArray :=
  if p.contains nl then (jDirty p b.toList).toByteArray else (p.toByteArray.push 10) ++ b

theorem jInputB_eq (p : Bytes) (b : ByteArray) : jInputB p b = (jInput p b.toList).toByteArray := by
  unfold jInputB jInput
  cases h : p.contains nl
  · simp only [Bool.false_eq_true, ite_false]
    apply ByteArray.ext
    apply Array.ext'
    simp [toList_eq, nl]
  · simp only [ite_true]

/-- The digest of a record whose body is flat. -/
def jLinkB (p : Bytes) (b : ByteArray) : Digest := hexOf (sha256 (jInputB p b)).toList

theorem jLinkB_eq (p : Bytes) (b : ByteArray) : jLinkB p b = jLink p b.toList := by
  simp [jLinkB, jLink, sha256L, jInputB_eq]

/-! ## The signature file -/

/-- Cut bytes at the first `x`. -/
def cutAt (x : UInt8) : Bytes → Option (Bytes × Bytes)
  | [] => none
  | b :: r => if b = x then some ([], r) else (cutAt x r).map fun p => (b :: p.1, p.2)

/-- `{"head":"` -/
def jHeadK : Bytes := [123, 34, 104, 101, 97, 100, 34, 58, 34]
/-- `,"index":` -/
def jIdxK : Bytes := [44, 34, 105, 110, 100, 101, 120, 34, 58]
/-- `"mac":"` -/
def jMacK : Bytes := [34, 109, 97, 99, 34, 58, 34]

/-- The signature file: `{"head":"<hex>","index":<n>,"mac":"<hex>"}`. -/
def jSigEnc (s : Sig) : Bytes := jHeadK ++ s.head ++ 34 :: jIdxK ++ natDec s.index ++ 44 :: jMacK ++ s.mac ++ jEnd

/-- Read the signature file back, in exactly the form it is written (`none` for anything else). -/
def jSigDec (t : Bytes) : Option Sig :=
  if startsL jHeadK t then
    match cutAt 34 (t.drop 9) with
    | none => none
    | some (h, r1) =>
      if startsL jIdxK r1 then
        match cutAt 44 (r1.drop 9) with
        | none => none
        | some (digits, r2) =>
          if startsL jMacK r2 then
            match stripSuf jEnd (r2.drop 7), parseDec digits with
            | some m, some n => some ⟨n, h, m⟩
            | _, _ => none
          else none
      else none
  else none

/-! ## The parameters -/

/-- **The JSON-lines journal**: SHA-256 chain, the line `{"c":"<hex>",…}`, the signature file `{"head":…,"index":…,"mac":…}`; `label` is the text whose hash is the digest
before the first record (the host's). -/
def Params.jsonl (label : Bytes) : Params where
  genesis := hexOf (sha256L label)
  link := jLink
  enc := jEnc
  dec := jDec
  frameLine := jFrame
  splitLine := jSplit
  sigEnc := jSigEnc
  sigDec := jSigDec
  linkB := jLinkB
  decB := jDecB
  splitB := jSplitB
  linkB_eq := jLinkB_eq
  decB_eq := jDecB_eq
  splitB_eq := jSplitB_eq

end VbmJournal
