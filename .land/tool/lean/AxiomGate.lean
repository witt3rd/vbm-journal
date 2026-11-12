import Lean
/-! The axiom gate of vbm-land (docs/lean-gates.md; run it with `land-lean axiom`): every constant defined in a module of the audited ROOTS may depend only on the three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`). Exits non-zero (and names the offenders) otherwise. The modules to import and the roots to audit are arguments, read by `land-lean` from the repository's
`.land/lean.conf` (the tool's one parser): `--imports A,B.C --roots X,Y`. A root that matches no constant is an error: a gate that audited nothing proves nothing.
`--selftest` also runs the differential test: the shared walk below must agree with Lean's own `collectAxioms` on real constants and on planted axioms of every kind, and it must catch deliberately broken walks. -/
open Lean

def allowed : List Name := [`propext, `Classical.choice, `Quot.sound]

/-- Per constant, with its own walk: names every (constant, axiom) offence. Quadratic in the number of constants (each call walks its own closure), so it only runs to
attribute a failure that `unionOk` has already found. -/
def audit (names : Array Name) : CoreM (Nat × Nat) := do
  let mut bad := 0
  for n in names do
    for a in (← collectAxioms n) do
      unless allowed.contains a do
        IO.eprintln s!"{n} depends on non-standard axiom {a}"
        bad := bad + 1
  return (names.size, bad)

/-- What a constant's axioms depend on directly: Lean's own `collectAxioms` rule (the type of an axiom, constructor or recursor; the type and value of a definition,
theorem or opaque; the type and the constructors of an inductive; nothing for the quotient constants). -/
def usedOf (ci : ConstantInfo) : Array Name :=
  match ci with
  | .axiomInfo v => v.type.getUsedConstants
  | .defnInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .thmInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .opaqueInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .quotInfo _ => #[]
  | .ctorInfo v => v.type.getUsedConstants
  | .recInfo v => v.type.getUsedConstants
  | .inductInfo v => v.type.getUsedConstants ++ v.ctors.toArray

/-- ONE walk over the union of the closures of `names`, every constant visited once: the axioms it meets are exactly the union of the axioms of each name. `used` is the
dependency rule (`usedOf`; the differential test also passes deliberately broken ones, which it must catch). -/
partial def unionAxioms (used : ConstantInfo → Array Name) (env : Environment) : List Name → NameSet → NameSet → NameSet
  | [], _, axs => axs
  | n :: rest, seen, axs =>
    if seen.contains n then unionAxioms used env rest seen axs else
    let seen := seen.insert n
    match env.find? n with
    | none => unionAxioms used env rest seen axs
    | some ci => unionAxioms used env ((used ci).toList ++ rest) seen (match ci with | .axiomInfo _ => axs.insert n | _ => axs)

/-- The gate: one shared walk; when it meets only allowed axioms every constant passes (each one's axioms are a subset of the union), and the count is `names.size`; when it
meets another, the per-constant audit names the offenders and counts them. -/
def check (names : Array Name) : CoreM (Nat × Nat) := do
  let axs := unionAxioms usedOf (← getEnv) names.toList {} {}
  if axs.toList.all allowed.contains then return (names.size, 0) else audit names

/-! The differential test (Tier 1, in `--selftest`): the old per-constant `audit` (Lean's `collectAxioms`, one call per constant) is the ORACLE, and the shared walk must agree
with it. Compared per constant (the SET of axioms, not only the verdict), and on the verdict and the offender set of a whole list. Not in the hot path. -/

def sameSet (a : Array Name) (b : NameSet) : Bool := a.size == b.toList.length && a.all b.contains

/-- Names on which the shared walk (with dependency rule `used`) and `collectAxioms` disagree about a constant's axiom set. -/
def disagree (used : ConstantInfo → Array Name) (names : Array Name) : CoreM (Array Name) := do
  let env ← getEnv
  let mut out := #[]
  for n in names do
    let old ← collectAxioms n
    unless sameSet old (unionAxioms used env [n] {} {}) do out := out.push n
  return out

/-- The offenders (constant, axiom) of the oracle over `names`, silently. -/
def oracleOffenders (names : Array Name) : CoreM (Array (Name × Name)) := do
  let mut out := #[]
  for n in names do
    for a in (← collectAxioms n) do
      unless allowed.contains a do out := out.push (n, a)
  return out

/-- Planted axioms, in every kind of constant: an axiom, a definition, a theorem, an opaque, an inductive (its constructor mentions the axiom), that constructor, the
inductive's recursor, and a definition whose type uses the quotient constants. Each is also wrapped in a chain of definitions (depth 1, depth 5) that mention it only
through the previous link. Returns the top constants of every chain and the clean constants (Init's, the quotient ones) to compare as well. -/
def plant : CoreM (Array Name × Array Name) := do
  let n := mkConst `Nat
  let P := mkConst ``False
  let ax (nm : Name) (ty : Expr) : CoreM Unit := addDecl (.axiomDecl { name := nm, levelParams := [], type := ty, isUnsafe := false })
  ax `fx.badP P; ax `fx.badT (mkSort 1)
  addDecl (.defnDecl { name := `fx.def, levelParams := [], type := P, value := mkConst `fx.badP, hints := .abbrev, safety := .safe })
  addDecl (.thmDecl { name := `fx.thm, levelParams := [], type := P, value := mkConst `fx.badP })
  addDecl (.opaqueDecl { name := `fx.opq, levelParams := [], type := P, value := mkConst `fx.badP, isUnsafe := false })
  addDecl (.inductDecl [] 0 [{ name := `fx.I, type := mkSort 1, ctors := [{ name := `fx.I.mk, type := .forallE `x (mkConst `fx.badT) (mkConst `fx.I) .default }] }] false)
  let quotTy := mkApp2 (mkConst ``Quot [Level.one]) n (.lam `a n (.lam `b n (mkConst ``True) .default) .default)
  addDecl (.defnDecl { name := `fx.qd, levelParams := [], type := .forallE `q quotTy P .default, value := .lam `q quotTy (mkConst `fx.badP) .default, hints := .abbrev, safety := .safe })
  -- a definition of type Prop that mentions the constant `b` (of type `T`) and nothing else: the link of a chain
  let link (nm : Name) (T : Expr) (b : Expr) : CoreM Unit :=
    addDecl (.defnDecl { name := nm, levelParams := [], type := mkSort 0, value := .app (.lam `_ T (mkConst ``True) .default) b, hints := .abbrev, safety := .safe })
  let env ← getEnv
  let recTy := ((env.find? `fx.I.rec).get!.instantiateTypeLevelParams [Level.zero])
  let mut tops : Array Name := #[]
  for (k, b, T) in [("axiom", mkConst `fx.badP, P), ("def", mkConst `fx.def, P), ("thm", mkConst `fx.thm, P), ("opaque", mkConst `fx.opq, P), ("quotdef", mkConst `fx.qd, .forallE `q quotTy P .default),
                    ("ctor", mkConst `fx.I.mk, .forallE `x (mkConst `fx.badT) (mkConst `fx.I) .default), ("rec", mkConst `fx.I.rec [Level.zero], recTy), ("induct", mkConst `fx.I, mkSort 1)] do
    let top0 := b.constName!
    tops := tops.push top0
    let l1 := Name.mkStr `fx s!"{k}.d1"
    link l1 T b; tops := tops.push l1
    let mut prev := l1
    for d in [2:6] do
      let nm := Name.mkStr `fx s!"{k}.d{d}"
      link nm (mkSort 0) (mkConst prev); prev := nm
    tops := tops.push prev
  return (tops, #[`Quot, `Quot.mk, `Quot.lift, `Quot.ind, `Nat.add_comm, `Classical.em, `propext, `Classical.choice, `Quot.sound])

/-- A module's root is one of the audited roots. -/
def ours (roots : List Name) (r : Name) : Bool := roots.contains r

/-- The comma-separated value of `--key`, or none. -/
def listArg (args : List String) (key : String) : List String :=
  match args.dropWhile (· != key) with
  | _ :: v :: _ => (v.splitOn ",").filter (· != "")
  | _ => []

/-- A dotted module name. -/
def modName (s : String) : Name := (s.splitOn ".").foldl Name.mkStr Name.anonymous

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let imports := (listArg args "--imports").map modName
  let roots := (listArg args "--roots").map modName
  if imports.isEmpty || roots.isEmpty then IO.eprintln "axiom gate: --imports and --roots are required (land-lean reads them from .land/lean.conf)"; return 2
  let env ← importModules (imports.toArray.map fun m => { module := m }) {}
  -- the constants of our modules, read from those modules' own data (not by filtering every imported constant)
  let mut names : Array Name := #[]
  for h : i in [0:env.header.moduleNames.size] do
    if ours roots env.header.moduleNames[i].getRoot then names := names ++ env.header.moduleData[i]!.constNames
  if names.isEmpty then IO.eprintln s!"axiom gate: no constants in the roots {roots}: a gate that audited nothing proves nothing (check .land/lean.conf)"; return 1
  let ((count, bad), _) ← (check names).toIO { fileName := "", fileMap := default } { env }
  IO.println s!"axiom gate: {count} constants checked, {bad} offending"
  if args.contains "--selftest" then
    -- the shared walk is not vacuous: it finds a standard axiom behind a real theorem
    unless (unionAxioms usedOf env [`Classical.em] {} {}).contains `Classical.choice do
      IO.eprintln "tier1: the axiom gate's shared walk does not find Classical.choice behind Classical.em"; return 1
    let ctx : Core.Context := { fileName := "", fileMap := default }
    -- the real proof set: every constant with AXIOM_DIFF_FULL=1 (about 2 CPU minutes), else every 40th (the oracle is the old quadratic audit); the shared walk's axiom set must equal Lean's, per constant
    let all := (← IO.getEnv "AXIOM_DIFF_FULL").isSome
    -- the constants checked are the constants of our modules: the module-data enumeration above equals the old filter over every imported constant (the printed count is the same; the
    -- filter scans about 170,000 constants in the interpreter, about 4 CPU s, so it runs with the full differential)
    if all then
      let mut oldNames : NameSet := {}
      for (n, _) in env.constants.map₁.toList do
        let some idx := env.getModuleIdxFor? n | continue
        if ours roots (env.header.moduleNames[idx.toNat]!).getRoot then oldNames := oldNames.insert n
      -- a module's data can hold a name another module's data holds too (the equation lemma `foo.eq_1`, generated in each module that unfolds `foo`): the oracle is a set, so compare the distinct names
      let distinct : NameSet := names.foldl (fun s n => s.insert n) {}
      unless oldNames.toList.length == distinct.toList.length && names.all oldNames.contains do
        IO.eprintln s!"tier1: the axiom gate checks {distinct.toList.length} distinct constants but the constants of our modules number {oldNames.toList.length}"; return 1
    let sample := if all then names else (Array.range names.size).filterMap fun i => if i % 40 == 0 then names[i]? else none
    let (real, _) ← (disagree usedOf sample).toIO ctx { env }
    unless real.isEmpty do IO.eprintln s!"tier1: the shared axiom walk and collectAxioms disagree on real constants: {real}"; return 1
    let selfTest : CoreM (Bool × String) := do
      let (tops, clean) ← plant
      let fx := tops ++ #[`fx.badT, `fx.I.rec]
      let mut msg := ""
      -- the fixtures are not vacuous: the oracle itself flags every planted top, and none of the clean constants
      for t in tops ++ #[`fx.badT] do
        if (← oracleOffenders #[t]).isEmpty then msg := msg ++ s!" the oracle flags nothing for the planted {t};"
      unless (← oracleOffenders clean).isEmpty do msg := msg ++ " the oracle flags a clean constant;"
      -- per constant: the shared walk's axiom SET equals the oracle's on every fixture and clean constant, at every depth (the planted ones: directly)
      let diff ← disagree usedOf (fx ++ clean)
      unless diff.isEmpty do msg := msg ++ s!" axiom sets differ on {diff};"
      -- the gate's verdict and offender set against the oracle's: each top alone, the whole set, and the planted ones among clean ones
      for group in tops.toList.map (#[·]) ++ [fx, tops ++ clean, clean] do
        let off ← oracleOffenders group
        let (_, nbad) ← check group
        let oldBad := off.size
        if (oldBad == 0) != (nbad == 0) then msg := msg ++ s!" verdicts differ on {group};"
        if oldBad != nbad then msg := msg ++ s!" offender counts differ on {group} ({oldBad} vs {nbad});"
      -- the differential can fail: shared walks that drop one kind of dependency must be caught on the fixtures
      let noCtors : ConstantInfo → Array Name := fun ci => match ci with | .inductInfo v => v.type.getUsedConstants | _ => usedOf ci
      let noValues : ConstantInfo → Array Name := fun ci => match ci with | .defnInfo v => v.type.getUsedConstants | .thmInfo v => v.type.getUsedConstants | .opaqueInfo v => v.type.getUsedConstants | _ => usedOf ci
      let noTypes : ConstantInfo → Array Name := fun ci => match ci with | .ctorInfo _ | .recInfo _ | .axiomInfo _ => #[] | _ => usedOf ci
      let nothing : ConstantInfo → Array Name := fun _ => #[]
      for (nm, mutant) in [("no-ctors", noCtors), ("no-values", noValues), ("no-types", noTypes), ("nothing", nothing)] do
        if (← disagree mutant (fx ++ clean)).isEmpty then msg := msg ++ s!" the differential does not catch the broken walk {nm};"
      -- and the gate itself rejects a planted axiom (in the same run)
      for t in tops do
        if (← check #[t]).2 == 0 then msg := msg ++ s!" the axiom gate accepted the planted {t};"
      return (msg.isEmpty, msg)
    let (out, ((ok, msg), _)) ← IO.FS.withIsolatedStreams (selfTest.toIO ctx { env })
    unless ok do IO.eprintln s!"tier1: the axiom gate's differential test failed:{msg}"; return 1
    IO.println s!"axiom gate: differential test ok (the shared walk equals the per-constant audit: axiom sets of {sample.size} of {names.size} real constants{if all then "" else " (a sample)"} and of planted axioms in every constant kind at depth 0, 1 and 5; four broken walks are caught)"
    IO.println "axiom gate: negative self-test ok (a constant on a non-standard axiom is rejected)"
  return if bad == 0 then 0 else 1
