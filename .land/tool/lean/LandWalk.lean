import Lean
open Lean
/-! # The reach walk (`land-lean ledger`; ClosureGate's walk in each repository is the same code)

Which definitions does an entry point run? The walk follows every constant a definition's body mentions (and its `implemented_by` and `_unsafe_rec`
bodies), skipping nothing but the CLOSED set of kinds in `auxKind`: a gate that hid every name with an underscore component hid every `private def`
and every lambda-lift, so a definition could leave the count by being renamed. After the `private` prefix is stripped, `_f` lambda-lifts,
`_sparseCasesOn_N` and `._unsafe_rec` bodies are definitions that decide, so they count. -/
namespace Land.Walk

/-- The closed set of definition kinds the gates do not count, by name. -/
def auxKind (env : Environment) (n : Name) : Option String :=
  if isAuxRecursor env n then some "auxRecursor"
  else if isNoConfusion env n then some "noConfusion"
  else if Meta.isMatcherCore env n then some "matcher"
  else if (env.getProjectionFnInfo? n).isSome then some "projection"
  else match env.find? n with
   | some (.ctorInfo _) => some "constructor" | some (.recInfo _) => some "recursor" | some (.inductInfo _) => some "inductive"
   | some (.quotInfo _) => some "quot" | some (.thmInfo _) => some "theorem" | some (.axiomInfo _) => some "axiom"
   | _ => match (privateToUserName? n).getD n with
     | .str _ s => if s == "_sunfold" || s == "_unfold" || s == "_boxed" || s.startsWith "_cstage" || s.startsWith "_proof_" then some "compiler-aux" else none
     | _ => none

def isAux (env : Environment) (n : Name) : Bool := (auxKind env n).isSome

/-- Every constant reachable from `todo` through definition bodies. -/
partial def walk (env : Environment) (todo : List Name) (seen : NameSet) : NameSet :=
  match todo with
  | [] => seen
  | n :: rest =>
    if seen.contains n then walk env rest seen else
    let seen := seen.insert n
    match env.find? n with
    | none => walk env rest seen
    | some ci =>
      let used : Array Name := (match ci.value? true with | some v => v.getUsedConstants | none => #[])
      let impl := (match Compiler.getImplementedBy? env n with | some i => [i] | none => []) ++
        (if (env.find? (Name.str n "_unsafe_rec")).isSome then [Name.str n "_unsafe_rec"] else [])
      walk env (used.toList ++ impl ++ rest) seen

/-- A constant of one of the subject's module roots. -/
def isSpec (roots : List Name) (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with | some i => roots.contains (env.header.moduleNames[i.toNat]!).getRoot | none => false

/-- A subject definition that is a function (a type or a predicate cannot be run). -/
def isFn (roots : List Name) (env : Environment) (n : Name) : Bool :=
  isSpec roots env n && !isAux env n && match env.find? n with
    | some ci => (let rec go : Expr → Bool | .forallE _ _ b _ => go b | .sort _ => false | _ => true; go ci.type)
    | none => false

/-- 2 = yes (every function the statement mentions is reached), 1 = partly, 0 = no (none is, or it mentions none). -/
def reachOf (roots : List Name) (env : Environment) (isReached : Name → Bool) (t : Name) : Nat :=
  let fs := ((env.find? t).map (·.type.getUsedConstants)).getD #[] |>.filter (isFn roots env)
  if fs.any isReached then (if fs.all isReached then 2 else 1) else 0

end Land.Walk
