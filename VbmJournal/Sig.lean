import VbmJournal.Sha256
/-! # vbm-journal slice 2, part 2: the signed head (`<journal>.sig`)

The hash chain makes an edit of some record detectable, but whoever can write the file can rebuild a consistent chain or cut the journal back
to an earlier point. So after every append the writer signs the chain head: `<journal>.sig` holds `index head mac`, where
`mac = hex(HMAC-SHA256(key, "index:head"))` and `index` is the number of records the head follows (lung's `Lung.Sign`, `LungSpec.JournalSig`).
The key is the host's (never in the journal, never here); `mac` below is the keyed function the host supplies.

Verification (`verdict`) **fails closed**: on a signature file that does not read, on a mac that is not the key's, on a journal cut back below the
signed index, and on a chain whose head at the signed index is not the signed head. Records after the signed index (a crash between an append
and the signature) are an **unsigned tail**: reported, accepted. No signature file means an unsigned journal (older), reported. -/
namespace VbmJournal

/-- The text the key's mac is taken of: `index:head`. -/
def macInput (index : Nat) (head : Digest) : Bytes := natDec index ++ 58 :: head

/-! ## Verification -/

/-- What verification found: no signature (an older journal), or a valid one with the number of records after the signed point. -/
inductive Verdict where
  | unsigned
  | signed (index unsignedTail : Nat)
  deriving DecidableEq, Repr

def macMsg : String := "journal signature: the mac does not match (wrong key, or the signature was edited)"
def unreadableMsg : String := "journal signature: unreadable"
def cutMsg (have_ index : Nat) : String :=
  s!"journal signature: the journal was cut back below its signed point ({have_} records, signed at {index})"
def rewrittenMsg (index : Nat) : String :=
  s!"journal signature: the chain at record {index} is not the signed head (the journal was rewritten)"

/-- A journal's verdict: `mac` is the key's mac (`mac index head`), `text` the signature file when there is one, `es` the journal's verified
entries. Fails closed. -/
def verdict (P : Params) (mac : Nat → Digest → Bytes) (es : List Entry) : Option Bytes → Except String Verdict
  | none => .ok .unsigned
  | some text =>
    match P.sigDec text with
    | none => .error unreadableMsg
    | some s =>
      if mac s.index s.head ≠ s.mac then .error macMsg
      else if es.length < s.index then .error (cutMsg es.length s.index)
      else if headFrom P P.genesis (es.take s.index) ≠ s.head then .error (rewrittenMsg s.index)
      else .ok (.signed s.index (es.length - s.index))

/-- The signature a writer makes of its head `h` after `c` records. -/
def Sig.make (mac : Nat → Digest → Bytes) (c : Nat) (h : Digest) : Sig := ⟨c, h, mac c h⟩

/-- The keyed mac of the real signature: `hex(HMAC-SHA256(key, "index:head"))`. -/
def macReal (key : Bytes) (index : Nat) (head : Digest) : Bytes := hexOf (hmacSha256 key (macInput index head))

end VbmJournal
