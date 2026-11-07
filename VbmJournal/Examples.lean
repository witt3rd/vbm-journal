import VbmJournal.Concrete
/-! # vbm-journal slice 1, part 5: the reference executable specification

Scripts of events run through `World.step` with the toy parameters, rendered as text. `golden` is what `tests/golden/slice1.golden`
holds; `VbmJournalProofs.Golden` compares them at build time, so a change of the model that changes a trace fails the build. To
regenerate the file after a deliberate change, print `VbmJournal.Examples.golden` (`#eval IO.print VbmJournal.Examples.golden`). -/
namespace VbmJournal.Examples

def P : Params := Params.toy

/-- The plan of an event, for showing: what the interpreter would do. -/
def showEffect : Effect → String
  | .write b => s!"write {(showBytes b).replace "\n" "\\n"}"
  | .fsync => "fsync"
  | .fsyncDir => "fsyncDir"
  | .readAll => "readAll"
  | .truncate n => s!"truncate {n}"

def showEntry : Entry → String
  | .note n => s!"note {n}"
  | .call i => s!"call {i}"
  | .done i b => s!"done {i} {if b then "interrupted" else "ok"}"

def showMode : Mode → String
  | .idle => "idle"
  | .opened => "opened"
  | .reading => "reading"
  | .ready _ c => s!"ready count={c}"
  | .busy _ c => s!"busy count={c}"
  | .broken => "broken"

/-- The file as the next reader finds it. -/
def showFile (bytes : Bytes) : String :=
  match read P bytes with
  | none => "verify: FAILED (fails closed)"
  | some r => s!"verify: ok entries=[{", ".intercalate (r.entries.map showEntry)}] head={showBytes r.head} torn={r.tail.length}"

def showEvent : WEvent → String
  | .takeOver => "takeOver"
  | .crash k v => s!"crash keep={k} vanish={v}"
  | .recover g none => s!"recover gen={g}"
  | .recover g (some c) => s!"recover gen={g} crash-after={c.n} keep={c.keep} vanish={c.vanish}"
  | .append g e none => s!"append gen={g} {showEntry e}"
  | .append g e (some c) => s!"append gen={g} {showEntry e} crash-after={c.n} keep={c.keep} vanish={c.vanish}"

/-- The plan the machine makes for the event (what the interpreter would perform), or `refused`. -/
def planOf (w : World) : WEvent → String
  | .append g e _ =>
    let (m1, plan) := step P w.m (.append g e)
    if m1 != w.m then "plan [" ++ "; ".intercalate (plan.map showEffect) ++ "]" else "refused"
  | .recover g _ =>
    let (m1, _) := step P w.m (.recover g)
    match m1.mode with
    | .reading =>
      let (m2, plan) := step P m1 (.readReply g w.fs.contents)
      if m2.mode == .broken then "refused to write: journal fails verification"
      else "plan [" ++ "; ".intercalate (Effect.readAll :: plan |>.map showEffect) ++ "]"
    | _ => "refused"
  | _ => ""

/-- Run a script, showing each event, its plan, and the file after it. -/
def trace (w0 : World) (evs : List WEvent) : String := Id.run do
  let mut w := w0
  let mut out := ""
  for ev in evs do
    let p := planOf w ev
    w := w.step P ev
    out := out ++ s!"  {showEvent ev}\n" ++ (if p = "" then "" else s!"    {p}\n")
      ++ s!"    gen={w.m.gen} mode={showMode w.m.mode} {showFile w.fs.contents}\n"
  return out

/-- The file as text, one line per record, with a marker for a torn tail. -/
def showLines (w : World) : String :=
  let (ls, t) := parseLines w.fs.contents
  "".intercalate (ls.map fun l => s!"    | {showBytes l}\n") ++ (if t = [] then "" else s!"    | {showBytes t} <torn tail>\n")

def opened : List WEvent := [.takeOver, .recover 1 none]

/-- 1. A journal that was never written. -/
def caseEmpty : String :=
  "## empty journal\n  start\n    " ++ showFile [] ++ "\n" ++ trace World.init opened

/-- 2. One record, and the file it leaves. -/
def caseOne : String :=
  let evs := opened ++ [.append 1 (.note 7) none]
  "## one record\n" ++ trace World.init evs ++ "  file\n" ++ showLines (World.init.run P evs)

/-- 3. A torn tail: a crash in the middle of the third append; recovery drops it; the acknowledged records survive. -/
def caseTorn : String :=
  let pre := opened ++ [.append 1 (.note 1) none, .append 1 (.note 2) none]
  let evs := [.append 1 (.note 3) (some ⟨1, 9, false⟩), .takeOver, .recover 2 none, .append 2 (.note 4) none]
  let w1 := World.init.run P pre
  "## torn tail\n" ++ trace World.init pre ++ "  file before the crash\n" ++ showLines w1
    ++ trace w1 evs ++ "  file after recovery and one more append\n" ++ showLines (w1.run P evs)

/-- 4. A stale writer: after the take-over, the old generation is refused and writes nothing. -/
def caseStale : String :=
  let pre := opened ++ [.append 1 (.note 1) none]
  let evs := [.takeOver, .append 1 (.note 99) none, .recover 1 none, .recover 2 none, .append 1 (.note 98) none, .append 2 (.note 2) none]
  let w1 := World.init.run P pre
  "## stale writer\n" ++ trace World.init pre ++ trace w1 evs ++ "  file\n" ++ showLines (w1.run P evs)

/-- 5. A call in flight at a crash: recovery settles it as interrupted, once; a second recovery adds nothing. -/
def caseInflight : String :=
  let pre := opened ++ [.append 1 (.call 5) none, .append 1 (.call 6) none, .append 1 (.done 5 false) none, .append 1 (.note 9) (some ⟨2, 0, false⟩)]
  let evs := [.takeOver, .recover 2 none, .takeOver, .recover 3 none]
  let w1 := World.init.run P pre
  "## call in flight\n" ++ trace World.init pre ++ trace w1 evs ++ "  file\n" ++ showLines (w1.run P evs)

/-- Flip the byte at the given index of a file's contents. -/
def flip (b : Bytes) (i : Nat) : Bytes := b.mapIdx fun j x => if j = i then x ^^^ 1 else x

/-- The file's lines, swapped in pairs, as bytes. -/
def swapFirstTwo (b : Bytes) : Bytes :=
  match parseLines b with
  | (l1 :: l2 :: rest, t) => frame l2 ++ frame l1 ++ (rest.map frame).foldr (· ++ ·) [] ++ t
  | _ => b

/-- 6. A chain tamper: an edited record, two reordered records, a deleted record (all fail verification), and a cut at the end (verifies: only the signed head, slice 2, catches it). -/
def caseTamper : String :=
  let evs := opened ++ [.append 1 (.note 1) none, .append 1 (.note 2) none, .append 1 (.note 3) none]
  let good := (World.init.run P evs).fs.contents
  let (ls, _) := parseLines good
  let dropMiddle := frame (ls.getD 0 []) ++ frame (ls.getD 2 [])
  let cutEnd := (ls.take 2).foldr (fun l acc => frame l ++ acc) []
  let body0 := (ls.getD 0 []).length - 1
  let w (b : Bytes) : World := ⟨⟨1, .opened⟩, ⟨b, [], true⟩⟩
  let recoverOn (b : Bytes) : String :=
    let (m, _) := step P (w b).m (.recover 1)
    let (m2, plan) := step P m (.readReply 1 b)
    s!"mode={showMode m2.mode} plan [{"; ".intercalate (plan.map showEffect)}]"
  "## chain tamper\n" ++
  s!"  intact\n    {showFile good}\n" ++
  s!"  record 1 edited (one byte of the body flipped)\n    {showFile (flip good body0)}\n    recovery: {recoverOn (flip good body0)}\n" ++
  s!"  records 1 and 2 swapped\n    {showFile (swapFirstTwo good)}\n" ++
  s!"  record 2 deleted\n    {showFile dropMiddle}\n" ++
  s!"  last record cut off (the chain alone cannot tell; the anchor does)\n    {showFile cutEnd}\n"

/-- The golden text. -/
def golden : String :=
  "# vbm-journal slice 1 golden (toy digest: FNV-1a 64, hex; slice 2 uses SHA-256)\n" ++
  caseEmpty ++ caseOne ++ caseTorn ++ caseStale ++ caseInflight ++ caseTamper

end VbmJournal.Examples
