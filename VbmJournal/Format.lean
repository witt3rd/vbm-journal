import VbmJournal.Bytes
/-! # vbm-journal slice 3, part 2: bytes, digests, and the plain-text formats of slices 1 and 2

The vocabulary the model is written in (`Bytes`, `Digest`, the newline and the separator), decimal numbers, the signature record (`Sig`), and the two plain-text
formats of slices 1 and 2: the line `digest ' ' body` and the signature file `index head mac`. They are the formats of `Params.ofLists`; another format (the
JSON lines of `VbmJournal.Json`) is another `Params`, since the line and the signature file are parameters (`Params.frameLine`, `splitLine`, `sigEnc`, `sigDec`). -/
namespace VbmJournal

/-- Bytes on disk. -/
abbrev Bytes := List UInt8

/-- A chain digest, as the bytes written in the line (lower-case hex). -/
abbrev Digest := Bytes

/-- The newline byte that ends a line. -/
def nl : UInt8 := 10

/-- The byte between a line's digest and its body. -/
def sp : UInt8 := 32

/-- Cut bytes into the part before the first separator and the part after it. -/
def splitSp : Bytes → Option (Digest × Bytes)
  | [] => none
  | b :: rest =>
    if b = sp then some ([], rest)
    else (splitSp rest).map fun p => (b :: p.1, p.2)

/-- A number in decimal. -/
def natDec (n : Nat) : Bytes :=
  if n < 10 then [(48 + n).toUInt8] else natDec (n / 10) ++ [(48 + n % 10).toUInt8]
termination_by n
decreasing_by omega

/-- A number read from decimal digits (`none` for nothing, or for anything that is not a digit). -/
def parseDec (b : Bytes) : Option Nat :=
  if !b.isEmpty && b.all (fun d => 48 ≤ d.toNat && d.toNat ≤ 57) then
    some (b.foldl (fun a d => a * 10 + (d.toNat - 48)) 0)
  else none

/-- What the signature file says: the number of records signed, the chain head after them, and the mac. -/
structure Sig where
  index : Nat
  head : Digest
  mac : Bytes
  deriving DecidableEq, Repr

/-- The signature file of slice 2: `index`, a space, `head`, a space, `mac`. -/
def Sig.toBytes (s : Sig) : Bytes := natDec s.index ++ sp :: (s.head ++ sp :: s.mac)

/-- Read the file back (`none` when it does not have the three fields). -/
def Sig.ofBytes (t : Bytes) : Option Sig :=
  match splitSp t with
  | none => none
  | some (i, rest) =>
    match parseDec i, splitSp rest with
    | some n, some (h, m) => some ⟨n, h, m⟩
    | _, _ => none

end VbmJournal
