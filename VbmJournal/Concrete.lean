import VbmJournal.World
/-! # vbm-journal slice 1, part 4: one concrete choice of the two parameters

For the reference examples and the golden file. The codec is unary and canonical (`Codec` laws are proved in
`VbmJournalProofs.Laws`). The digest is a **toy**: FNV-1a over `prev ++ "\n" ++ body`, 16 hex digits. It makes the examples
readable and deterministic; it is not collision resistant and the chain-integrity theorems do not hold for it. They are about any
digest that binds (`Hash.Binding`); slice 2 supplies SHA-256 as a shim. -/
namespace VbmJournal

/-- A string as bytes (ASCII). -/
def ascii (s : String) : Bytes := s.toList.map fun c => c.toNat.toUInt8

/-- Bytes as a string (one character per byte), for showing. -/
def showBytes (b : Bytes) : String := String.ofList (b.map fun x => Char.ofNat x.toNat)

/-- The codec: a tag, then the number in unary (`1` repeated). -/
def encUnary : Entry → Bytes
  | .note n => 110 :: List.replicate n 49
  | .call id => 99 :: List.replicate id 49
  | .done id true => 100 :: 105 :: List.replicate id 49
  | .done id false => 100 :: 107 :: List.replicate id 49

/-- The inverse of `encUnary`; `none` on anything else. -/
def decUnary : Bytes → Option Entry
  | 110 :: r => if r.all (· == 49) then some (.note r.length) else none
  | 99 :: r => if r.all (· == 49) then some (.call r.length) else none
  | 100 :: 105 :: r => if r.all (· == 49) then some (.done r.length true) else none
  | 100 :: 107 :: r => if r.all (· == 49) then some (.done r.length false) else none
  | _ => none

/-- A lower-case hex digit. -/
def hexDigit (n : Nat) : UInt8 := (if n < 10 then 48 + n else 87 + n).toUInt8

/-- Sixteen hex digits of a number below 2^64. -/
def hex16 (n : Nat) : Bytes := (List.range 16).reverse.map fun i => hexDigit (n / 16 ^ i % 16)

/-- FNV-1a, 64 bits. -/
def fnv (b : Bytes) : Nat :=
  b.foldl (fun h x => ((h ^^^ x.toNat) * 1099511628211) % 2 ^ 64) 14695981039346656037

/-- The toy parameters. -/
def Params.toy : Params where
  genesis := hex16 (fnv (ascii "vbm-journal-v1"))
  link prev body := hex16 (fnv (prev ++ nl :: body))
  enc := encUnary
  dec := decUnary

end VbmJournal
