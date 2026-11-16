import Lean
/-! # The obligation ledger's vocabulary (`land-lean ledger`, docs/lean-gates.md)

Every claim a library makes, keyed by a slug. A claim is `proved` only by naming theorems (double-backtick names are checked at elaboration, so a
renamed or deleted theorem breaks the repository's `Ledger.lean`), `partly` when theorems cover only a part (the note says which part is open),
`open_` when nothing is proved, or `limit` when no machine decides it (the note says who carries it).

The tool ships these types, so that ONE gate (`lean/LedgerGate.lean`) serves every repository: a repository's `Ledger.lean` imports `LandLedger`,
opens `Land.Ledger`, and holds only its data, `def ledger : List Obligation`. A claim may carry clause tags (`OC`: the parts of a standard it is
about, checked against the repository's clause index) and a caveat (what the ledger adds to a claim the theorems do not say by themselves: it
lives with the claim, never in the gate). -/
namespace Land.Ledger

inductive Status where
  | proved (thms : List Lean.Name)
  | partly (thms : List Lean.Name) (open_ : String)
  | open_ (note : String)
  | limit (carriedBy : String)

structure Obligation where
  slug    : String
  status  : Status
  clauses : List String := []
  caveat  : String := ""

/-- A claim with no clause tags. -/
def O (slug : String) (s : Status) : Obligation := { slug, status := s }
/-- A claim tagged with the clauses of a standard it is about. -/
def OC (slug : String) (clauses : List String) (s : Status) : Obligation := { slug, status := s, clauses }
/-- The same claim, with a caveat the generated ledger prints beside it. -/
def Obligation.withCaveat (o : Obligation) (c : String) : Obligation := { o with caveat := c }

end Land.Ledger
