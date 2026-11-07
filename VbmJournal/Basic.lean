import VbmJournal.Bytes
import VbmJournal.Format
import VbmJournal.Scan
/-! # vbm-journal slice 1, part 1: records, lines and the digest chain

The pure model of lung's journal (`impl/Lung/Jnl.lean`, `impl/Lung/JournalIO.lean`, `substrate/journal.c`). `Init` only: this
file is compiled and linked, so it has no `Std` and no `Lean` import, no IO and no axiom.

The file is a sequence of **lines**. A line is `digest ++ [' '] ++ body`, followed by one newline byte; the body is the encoded entry
and the digest is `link prev body`, where `prev` is the digest of the line before (`genesis` for the first). The digest of the
last line is the journal's **head**; it binds every byte before it. A final fragment without a newline is a **torn tail**
(a crash in the middle of a write); a reader drops it.

Two things are parameters, because the model must not choose them: the digest function (`link`, SHA-256 in lung; the shim of
slice 2) and the entry codec (`enc` and `dec`; JSON in lung). What the proofs need of each is stated as laws in
`VbmJournalProofs.Laws`, not assumed here. -/
namespace VbmJournal

/-- Is this a well-formed host record: a JSON object that begins with a key (`{"`), has no newline (it is one line) and does not begin with the key `vbm`
(which the library's own entries use in the JSON-lines format, `VbmJournal.Json`)? -/
def bodyWf (l : Bytes) : Bool :=
  l.take 2 == [123, 34] && l.take 6 != [123, 34, 118, 98, 109, 34] && !l.contains nl

/-- A record that belongs to the host (the journal's user): the bytes of its line, opaque to the library. A host maps its own records onto `Entry.body`
(its JSON text) and back; the library chains, verifies, recovers and signs them as it does the others. The bytes are a flat buffer: a journal of
megabytes holds its records without a list cell per byte. -/
structure Body where
  bytes : ByteArray
  wf : bodyWf bytes.toList = true

instance : DecidableEq Body := fun a b =>
  if h : a.bytes.toList = b.bytes.toList then
    isTrue (by
      obtain ⟨a1, a2⟩ := a
      obtain ⟨b1, b2⟩ := b
      have : a1 = b1 := by rw [← toByteArray_toList a1, ← toByteArray_toList b1]; exact congrArg List.toByteArray h
      subst this
      rfl)
  else isFalse (fun e => h (by subst e; rfl))

instance : Repr Body := ⟨fun b _ => repr b.bytes.toList⟩

/-- What a journal records. `call` is a request sent and not yet answered, `done` its completion (`interrupted` is the recovery's verdict), `note` a record
with a number (a handle on content kept elsewhere), `body` a record of the host's own (its text, `Body`). Only `call` and `done` mean anything to
recovery: a journal without them has nothing in flight and recovery adds nothing to it. -/
inductive Entry where
  | note (n : Nat)
  | call (id : Nat)
  | done (id : Nat) (interrupted : Bool)
  | body (b : Body)
  deriving DecidableEq, Repr

/-- The parameters: the digest chain, the entry codec, the line and the signature file, and their flat-buffer forms.

The model leaves all of these open, because it must not choose them: the digest (`link`: SHA-256), the codec of an entry (`enc`, `dec`), how a digest and a body make
a line (`frameLine`) and how a line is cut back into them (`splitLine`), and how the signature is written (`sigEnc`, `sigDec`). What the proofs need of each is
stated as laws, `Params.Lawful` (`VbmJournalProofs.Laws`), and proved for each concrete choice.

`linkB`, `decB` and `splitB` are `link`, `dec` and `splitLine` on a `ByteArray`: what the compiled reader calls on the bytes of a journal of megabytes, so that it never
makes a list cell per byte (the proofs keep the list shape; `linkB_eq`, `decB_eq` and `splitB_eq` are the refinement). `Params.ofLists` makes them by conversion; a format
that can do better supplies its own with the proofs. -/
structure Params where
  genesis : Digest
  link : Digest → Bytes → Digest
  enc : Entry → Bytes
  dec : Bytes → Option Entry
  frameLine : Digest → Bytes → Bytes
  splitLine : Bytes → Option (Digest × Bytes)
  sigEnc : Sig → Bytes
  sigDec : Bytes → Option Sig
  linkB : Digest → ByteArray → Digest
  decB : ByteArray → Option Entry
  splitB : ByteArray → Option (Digest × ByteArray)
  linkB_eq : ∀ p b, linkB p b = link p b.toList
  decB_eq : ∀ b, decB b = dec b.toList
  splitB_eq : ∀ l, (splitB l).map (fun q => (q.1, q.2.toList)) = splitLine l.toList

/-- Parameters from the list-shaped digest and codec, with the plain-text line (`digest ' ' body`) and signature file (`index head mac`) of slices 1 and 2;
the flat forms of the digest and the codec by conversion. -/
def Params.ofLists (genesis : Digest) (link : Digest → Bytes → Digest) (enc : Entry → Bytes) (dec : Bytes → Option Entry) : Params where
  genesis := genesis
  link := link
  enc := enc
  dec := dec
  frameLine d b := d ++ sp :: b
  splitLine := splitSp
  sigEnc := Sig.toBytes
  sigDec := Sig.ofBytes
  linkB p b := link p b.toList
  decB b := dec b.toList
  splitB := splitSpB
  linkB_eq _ _ := rfl
  decB_eq _ := rfl
  splitB_eq := splitSpB_eq

/-- The line of an entry after the digest `prev` (without its newline). -/
def lineOf (P : Params) (prev : Digest) (e : Entry) : Bytes :=
  P.frameLine (P.link prev (P.enc e)) (P.enc e)

/-- A line as written: the line and its newline. -/
def frame (l : Bytes) : Bytes := l ++ [nl]

/-- The digest after the entries `es`, starting from `prev`. -/
def headFrom (P : Params) : Digest → List Entry → Digest
  | prev, [] => prev
  | prev, e :: es => headFrom P (P.link prev (P.enc e)) es

/-- The lines (without newlines) that the entries `es` make after the digest `prev`. -/
def sealAll (P : Params) : Digest → List Entry → List Bytes
  | _, [] => []
  | prev, e :: es => lineOf P prev e :: sealAll P (P.link prev (P.enc e)) es

/-- The bytes of the entries `es` after the digest `prev`: every line with its newline. -/
def encodeFrom (P : Params) : Digest → List Entry → Bytes
  | _, [] => []
  | prev, e :: es => frame (lineOf P prev e) ++ encodeFrom P (P.link prev (P.enc e)) es

/-! ## Reading -/

/-- Split bytes into complete lines and the final fragment that has no newline (the torn tail, empty when the bytes end in a newline). -/
def parseLines : Bytes → List Bytes × Bytes
  | [] => ([], [])
  | b :: rest =>
    let r := parseLines rest
    if b = nl then ([] :: r.1, r.2)
    else match r with
      | ([], t) => ([], b :: t)
      | (l :: ls, t) => ((b :: l) :: ls, t)

/-- Verify lines from the digest `prev`: each line's digest is `link` of the previous digest and its body, and its body decodes.
Returns the entries and the head, or `none` on the first line that fails (fail closed). -/
def verifyFrom (P : Params) : Digest → List Bytes → Option (List Entry × Digest)
  | prev, [] => some ([], prev)
  | prev, l :: ls =>
    match P.splitLine l with
    | none => none
    | some (d, body) =>
      if P.link prev body = d then
        match P.dec body with
        | none => none
        | some e => (verifyFrom P d ls).map fun p => (e :: p.1, p.2)
      else none

/-- What reading a journal's bytes finds: the verified entries, the head, and the torn tail that was dropped. -/
structure Read where
  entries : List Entry
  head : Digest
  tail : Bytes
  deriving DecidableEq, Repr

/-- Read a journal's bytes: drop a torn tail, verify the whole chain from `genesis`. `none` is a journal that fails verification. -/
def read (P : Params) (bytes : Bytes) : Option Read :=
  match parseLines bytes with
  | (ls, tail) => (verifyFrom P P.genesis ls).map fun p => ⟨p.1, p.2, tail⟩

/-! ## Reading a flat buffer

The compiled reader works on the file's `ByteArray` (a flat buffer: one byte per byte), by index, in a loop: it never makes a list of the file's bytes and
never recurses once per line. `readB` is the same function as `read` on the bytes' list (`VbmJournalProofs.Flat`, `readB_eq`: the refinement). -/

set_option linter.unusedVariables false in
/-- `verifyFrom` over the lines of the flat buffer `b` from index `i` on, a loop: the entries so far (last first), the head, and the index where the
fragment without a newline begins (the torn tail). -/
def verifyB (P : Params) (b : ByteArray) (i : Nat) (prev : Digest) (acc : List Entry) : Option (List Entry × Digest × Nat) :=
  match h : findByte b nl i with
  | none => some (acc, prev, i)
  | some j =>
    match P.splitB (b.extract i j) with
    | none => none
    | some (d, body) =>
      if P.linkB prev body = d then
        match P.decB body with
        | none => none
        | some e => verifyB P b (j + 1) d (e :: acc)
      else none
termination_by b.size - i
decreasing_by
  have := findByte_lt b nl i _ h
  omega

/-- `read` on a flat buffer. -/
def readB (P : Params) (b : ByteArray) : Option Read :=
  match verifyB P b 0 P.genesis [] with
  | none => none
  | some (acc, h, ts) => some ⟨acc.reverse, h, (b.extract ts b.size).toList⟩

/-! ## Calls in flight -/

/-- One entry's effect on the list of calls that are open (called, not completed), in the order they were called. -/
def openStep (o : List Nat) : Entry → List Nat
  | .call id => if id ∈ o then o else o ++ [id]
  | .done id _ => o.filter fun i => i != id
  | .note _ => o
  | .body _ => o

/-- The calls in flight: made, and not completed. A journal that ends with one means the process died. -/
def openCalls (es : List Entry) : List Nat := es.foldl openStep []

/-- Recovery's settlement of a journal: every call in flight completes as interrupted, once, in the order called. -/
def settleEntries (es : List Entry) : List Entry := (openCalls es).map fun id => .done id true

end VbmJournal
