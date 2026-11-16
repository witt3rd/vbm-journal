import Lean
import LandLedger
import LandWalk
open Lean Land.Ledger Land.Walk
/-! # The ledger gate (`land-lean ledger`; docs/lean-gates.md)

Renders `docs/proof-ledger.md` from a repository's `def ledger : List Obligation` (the module it names, imported at run time), checks that every named
theorem exists and is a theorem, and, as the configuration asks:
* REACH (an entries file): "proved" means proved about code the entry points run. The gate walks the definitions they reach (`LandWalk`) and classes
  every cited theorem by the subject's functions its statement mentions: yes (every one is reached), partly (some), no (none: the statement is about a
  model nothing runs). A claim whose cited theorems are all `no` is shown as partial, not proved. A definition no entry names but run through a
  refinement theorem (the bridges file: `spec-def theorem reached-def`) counts as reached; the theorem must exist and mention both names.
* RATCHET (a baseline file): proved may only rise; open may only rise by the claims newly written down. `--write` rewrites the baseline.
* CLAUSES (an index file, one tag per line: the first word): every tag a claim cites must be in the index; with TAGGED, a proved or partial claim must also cite one.
  With COVERAGE dispositions (the second word of an index line), the clauses of those dispositions that no proved or partial claim tags are listed.
`--selftest` proves the gate can fail, in this same process. Exit 0 ok, 1 a check failed. -/

def readLines (p : String) : IO (List String) := do
  if !(← System.FilePath.pathExists p) then return []
  return (← IO.FS.readFile p).splitOn "\n" |>.map String.trimAscii |>.map (·.toString) |>.filter (fun l => l != "" && !l.startsWith "#")

def words (l : String) : List String := (l.splitOn " ").filter (· != "")

def namesOf (o : Obligation) : List Name := match o.status with | .proved l => l | .partly l _ => l | _ => []
def isCovering (o : Obligation) : Bool := match o.status with | .proved _ => true | .partly _ _ => true | _ => false

/-- The theorems a claim names that are not theorems. -/
def theoremErrors (env : Environment) (o : Obligation) : List String :=
  (namesOf o).filterMap fun n => match env.find? n with
    | some (.thmInfo _) => none
    | _ => some s!"ledger: {o.slug} names {n}, which is not a theorem"

/-- Tags a claim cites that the index does not list, and (when the repository asks for it) a covering claim that cites none. -/
def clauseErrors (tagged : Bool) (tags : List String) (l : List Obligation) : List String :=
  l.flatMap fun o =>
    (if tagged && isCovering o && o.clauses.isEmpty then [s!"ledger: claim {o.slug} cites no clause (the clause index lists what a claim may cite)"] else []) ++
    o.clauses.filterMap fun c => if tags.contains c then none else some s!"ledger: claim {o.slug} cites the clause {c}, which the clause index does not list"

/-- The verdict on a baseline: how many ratchets it breaks. -/
def ratchet (proved openN total : Nat) (baseL : List String) : List String :=
  let get (k : String) : Nat := (baseL.filterMap fun l => match l.splitOn " " with | [a, b] => if a == k then b.toNat? else none | _ => none).headD 0
  (if proved < get "proved" then [s!"ledger: proved fell from {get "proved"} to {proved}"] else []) ++
  -- open may rise only by the claims newly written down (a discovered obligation is honest; an old one silently reopened is not)
  (if baseL.length > 1 && openN > get "open" + (total - get "total") then [s!"ledger: open rose from {get "open"} to {openN} with {total - get "total"} new claim(s)"] else [])

unsafe def run (args : List String) : IO UInt32 := do
  let arg (k : String) : Option String := match args.dropWhile (· != k) with | _ :: v :: _ => some v | _ => none
  let list (k : String) : List String := ((arg k).getD "").splitOn "," |>.filter (· != "")
  let some modName := arg "--module" | IO.eprintln "ledger: --module is required"; return 2
  let constName := (arg "--constant").getD "ledger"
  let subject := (list "--subject").map String.toName
  let imports := (list "--imports").map String.toName
  initSearchPath (← findSysroot)
  let env ← importModules ((modName.toName :: imports).toArray.map fun m => { module := m }) {}
  let ledger ← match env.evalConst (List Obligation) {} constName.toName with
    | .ok l => pure l
    | .error e => IO.eprintln s!"ledger: cannot read {constName} of {modName}: {e}"; return 1
  let mut bad := 0
  -- reach
  let entries := (← readLines ((arg "--entries").getD "")).map String.toName
  for e in entries do
    if (env.find? e).isNone then IO.eprintln s!"ledger: entry point {e} is not in the environment"; bad := bad + 1
  let applyReach := (arg "--entries").isSome && !entries.isEmpty
  let reach := walk env entries {}
  let nReach := reach.toList.filter (fun n => isSpec subject env n && !isAux env n && (match env.find? n with | some (.defnInfo _) | some (.opaqueInfo _) => true | _ => false)) |>.length
  if applyReach then IO.println s!"ledger: reach: {nReach} subject definitions reachable from the entry points ({entries.length} entry points)"
  let mut bridged : NameSet := {}
  for l in ← readLines ((arg "--bridges").getD "") do
    match (words l).map String.toName with
    | [a, thm, b] =>
      let ok := reach.contains b && match env.find? thm with
        | some (.thmInfo ci) => ci.type.getUsedConstants.contains a && ci.type.getUsedConstants.contains b | _ => false
      if ok then bridged := bridged.insert a else IO.eprintln s!"ledger: bridge {a} is not backed: {thm} must be a theorem mentioning {a} and {b}, and {b} must be reached"; bad := bad + 1
    | _ => pure ()
  let isReached (n : Name) := reach.contains n || bridged.contains n
  -- clauses
  let idx := (← readLines ((arg "--clauses").getD "")).map words
  let haveClauses := (arg "--clauses").isSome
  let tags := idx.filterMap (·.head?)
  let tagged := args.contains "--tagged"
  if haveClauses then for e in clauseErrors tagged tags ledger do IO.eprintln e; bad := bad + 1
  let wantDisp := list "--coverage"
  let wanted := idx.filter fun ws => match ws with | t :: d :: _ => wantDisp.contains d && !t.isEmpty | _ => false
  let wantedTags := wanted.filterMap (·.head?)
  let uncovered := wantedTags.filter fun t => !(ledger.any fun o => isCovering o && o.clauses.contains t)
  -- the claims
  let mut proved := 0; let mut part := 0; let mut openN := 0; let mut lim := 0; let mut demoted := 0
  let mut seenThm : NameSet := {}; let mut yesThm := 0; let mut partlyThm := 0; let mut noThm := 0; let mut provedYes := 0
  let mut rows : Array String := #[]
  for o in ledger do
    for e in theoremErrors env o do IO.eprintln e; bad := bad + 1
    let names := namesOf o
    let cls := names.map (reachOf subject env isReached)
    let k := cls.filter (· == 2) |>.length
    for (n, c) in names.zip cls do
      unless seenThm.contains n do
        seenThm := seenThm.insert n
        if c == 2 then yesThm := yesThm + 1 else if c == 1 then partlyThm := partlyThm + 1 else noThm := noThm + 1
    let reached := if names.isEmpty || !applyReach then "-" else if cls.all (· == 2) then "yes" else if cls.all (· == 0) then "no" else s!"partly ({k} of {names.length})"
    let tag (n : Name) : String := if !applyReach then "" else match reachOf subject env isReached n with | 2 => "" | 1 => " ‡" | _ => " †"
    let thmList (l : List Name) : String := ", ".intercalate (l.map fun n => s!"`{n}`{tag n}")
    let cav := if o.caveat.isEmpty then "" else s!"; caveat: {o.caveat}"
    let cl := if o.clauses.isEmpty then "-" else ", ".intercalate (o.clauses.map fun c => s!"`{c}`")
    let row (status reach what : String) : String :=
      "| `" ++ o.slug ++ "` |" ++ (if haveClauses then s!" {cl} |" else "") ++ s!" {status} |" ++ (if applyReach then s!" {reach} |" else "") ++ s!" {what} |"
    match o.status with
    | .proved l =>
      if applyReach && cls.all (· == 0) && !l.isEmpty then
        demoted := demoted + 1; part := part + 1
        rows := rows.push (row "partial" reached s!"{thmList l}; open: not reached by the entry points: every cited theorem is about a model they never run (demoted from proved by the reach rule){cav}")
      else
        proved := proved + 1; if k == l.length then provedYes := provedYes + 1
        rows := rows.push (row "**proved**" reached s!"{thmList l}{cav}")
    | .partly l n => part := part + 1; rows := rows.push (row "partial" reached s!"{thmList l}; open: {n}{cav}")
    | .open_ n => openN := openN + 1; rows := rows.push (row "open" "-" n)
    | .limit n => lim := lim + 1; rows := rows.push (row "limit" "-" n)
  let total := ledger.length
  let head := "| claim (slug) |" ++ (if haveClauses then " clauses |" else "") ++ " status |" ++ (if applyReach then " reached by the entry points |" else "") ++ " theorems" ++ (if applyReach then " († model-only, ‡ partly)" else "") ++ ", and what is still open |\n"
  let sep := "|---|" ++ (if haveClauses then "---|" else "") ++ "---|" ++ (if applyReach then "---|" else "") ++ "---|\n"
  let md := s!"# Obligation ledger\n\nGenerated by `land-lean ledger` from `{modName}`; do not edit.\n" ++
    s!"\n**{proved} proved, {part} partial, {openN} open, {lim} limit, of {total}.** Only `proved` may be called verified" ++
    (if applyReach then s!", and `proved` means proved about code the entry points run: a claim whose cited theorems are all about models they never run is partial ({demoted} demoted by this rule)" else "") ++
    ". A `limit` is a claim no machine decides.\n\n" ++
    (if applyReach then s!"**reached by the entry points:** {yesThm} of {seenThm.size} cited theorems are about functions they reach (yes), {partlyThm} about some of them (partly ‡), {noThm} about none (no †).\n\n" else "") ++
    (if wantDisp.isEmpty then "" else s!"**Clause coverage: {wantedTags.length - uncovered.length} of {wantedTags.length} clauses** ({", ".intercalate wantDisp}) are tagged by a proved or partial claim; coverage is traceability from clause to theorem, never fidelity of the statement (that is a `limit`).\n\n" ++
      (if uncovered.isEmpty then "" else s!"Clauses with no covering claim: {", ".intercalate (uncovered.map (s!"`{·}`"))}.\n\n")) ++
    head ++ sep ++ "\n".intercalate rows.toList ++ "\n"
  if bad == 0 && !args.contains "--no-write" then IO.FS.writeFile "docs/proof-ledger.md" md
  IO.println s!"ledger: {proved} proved, {part} partial, {openN} open, {lim} limit, of {total}"
  if applyReach then IO.println s!"ledger: reached by the entry points: {yesThm} yes, {partlyThm} partly, {noThm} no of {seenThm.size} cited theorems; {provedYes} of {proved} proved claims fully reached; {demoted} demoted"
  if !wantDisp.isEmpty then IO.println s!"ledger: clause coverage {wantedTags.length - uncovered.length} of {wantedTags.length}"
  -- the ratchet
  let baseFile := (arg "--baseline").getD ""
  if (arg "--baseline").isSome then
    let baseL := (← (do if ← System.FilePath.pathExists baseFile then IO.FS.readFile baseFile else pure "")).splitOn "\n"
    if args.contains "--write" then
      let notes := baseL.filter (·.startsWith "#")   -- comment lines (the documented re-bases) are kept
      IO.FS.writeFile baseFile (("\n".intercalate notes) ++ (if notes.isEmpty then "" else "\n") ++ s!"proved {proved}\nopen {openN}\ntotal {total}\n")
      return 0
    for e in ratchet proved openN total baseL do IO.eprintln e; bad := bad + 1
  -- `--selftest`: the gate can fail, in this same process
  if args.contains "--selftest" && bad == 0 then
    let must (what : String) (errs : List String) : IO Bool := do
      if errs.isEmpty then IO.eprintln s!"ledger gate: it cannot fail ({what})"; return false else return true
    let mut ok := true
    ok := ok && (← must "a named constant that is not a theorem" (theoremErrors env (O "selftest" (.proved [`Nat.add]))))
    ok := ok && (← must "a named theorem that does not exist" (theoremErrors env (O "selftest" (.proved [`No.Such.Theorem]))))
    if (arg "--baseline").isSome then
      ok := ok && (← must "a baseline claiming more proved than exist" (ratchet proved openN total ["proved 9999", "open 0", s!"total {total}"]))
      if openN > 0 then ok := ok && (← must "open rising with no new claim" (ratchet proved openN total ["proved 0", s!"open {openN - 1}", s!"total {total}"]))
    if haveClauses then
      ok := ok && (← must "a clause tag that is not in the index" (clauseErrors tagged tags [OC "selftest" ["no-such-clause"] (.open_ "x")]))
      if tagged then ok := ok && (← must "a proved claim with no clause" (clauseErrors tagged tags [O "selftest" (.proved [`Nat.add_comm])]))
    if !ok then return 1
    IO.println "ledger gate: negative self-tests ok"
  return if bad == 0 then 0 else 1

unsafe def main (args : List String) : IO UInt32 := run args
