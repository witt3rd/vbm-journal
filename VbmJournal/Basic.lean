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

/-- Bytes on disk. -/
abbrev Bytes := List UInt8

/-- A chain digest, as the bytes written in the line (lower-case hex in lung). -/
abbrev Digest := Bytes

/-- What a journal records. `call` is a request sent and not yet answered (lung's `Action.run`), `done` its completion
(`Action.complete`; `interrupted` is the recovery's verdict), `note` every other record (`inject`, `cancel`, `restart`,
`put`, and the machine's input events: a handle on the content). -/
inductive Entry where
  | note (n : Nat)
  | call (id : Nat)
  | done (id : Nat) (interrupted : Bool)
  deriving DecidableEq, Repr

/-- The two parameters: the digest chain and the entry codec. -/
structure Params where
  genesis : Digest
  link : Digest → Bytes → Digest
  enc : Entry → Bytes
  dec : Bytes → Option Entry

/-- The newline byte that ends a line. -/
def nl : UInt8 := 10

/-- The byte between a line's digest and its body. -/
def sp : UInt8 := 32

/-- The line of an entry after the digest `prev` (without its newline). -/
def lineOf (P : Params) (prev : Digest) (e : Entry) : Bytes :=
  P.link prev (P.enc e) ++ sp :: P.enc e

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

/-- Cut a line into its digest and its body at the first separator. -/
def splitLine : Bytes → Option (Digest × Bytes)
  | [] => none
  | b :: rest =>
    if b = sp then some ([], rest)
    else (splitLine rest).map fun p => (b :: p.1, p.2)

/-- Verify lines from the digest `prev`: each line's digest is `link` of the previous digest and its body, and its body decodes.
Returns the entries and the head, or `none` on the first line that fails (fail closed). -/
def verifyFrom (P : Params) : Digest → List Bytes → Option (List Entry × Digest)
  | prev, [] => some ([], prev)
  | prev, l :: ls =>
    match splitLine l with
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

/-! ## Calls in flight -/

/-- One entry's effect on the list of calls that are open (called, not completed), in the order they were called. -/
def openStep (o : List Nat) : Entry → List Nat
  | .call id => if id ∈ o then o else o ++ [id]
  | .done id _ => o.filter fun i => i != id
  | .note _ => o

/-- The calls in flight: made, and not completed. A journal that ends with one means the process died. -/
def openCalls (es : List Entry) : List Nat := es.foldl openStep []

/-- Recovery's settlement of a journal: every call in flight completes as interrupted, once, in the order called. -/
def settleEntries (es : List Entry) : List Entry := (openCalls es).map fun id => .done id true

end VbmJournal
