import VbmJournal
/-! The tests of slice 2 (Tier 1). Not part of the library, never linked into it.

* `vbm-journal-test` (no argument): the shims against their models (SHA-256 and HMAC known answers, C against the Lean model on random inputs; every
  real file effect against the model file), and the differential test: the driver over the REAL shims against the slice 1 model (`World.step`) on the
  golden cases, the tampered files, and random scripts with crashes at every kind of point.
* `vbm-journal-test writer PATH`, `vbm-journal-test verify PATH ACKS`: the real crash test (`tests/crash.sh`): a writer is killed in the middle of its
  appends, and the journal is recovered. -/
open VbmJournal

def key : Bytes := ascii "test-key"
def macK : Nat → Digest → Bytes := macReal key

def fail (msg : String) : IO Unit := do
  IO.println s!"FAIL {msg}"
  IO.Process.exit 1

def expect (ok : Bool) (msg : String) : IO Unit := if ok then pure () else fail msg

/-! ## The hash shims -/

def hex (b : Bytes) : String := showBytes (hexOf b)

def shaTests : IO Unit := do
  expect (hex (sha256L (ascii "abc")) == "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad") "sha256 abc"
  expect (hex (sha256L []) == "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855") "sha256 empty"
  expect (hex (sha256L (ascii "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq")) ==
    "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1") "sha256 two blocks"
  expect (hex (sha256L (List.replicate 1000000 97)) == "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0") "sha256 million a"
  -- RFC 4231
  expect (hex (hmacSha256 (List.replicate 20 0x0b) (ascii "Hi There")) == "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7") "hmac 1"
  expect (hex (hmacSha256 (ascii "Jefe") (ascii "what do ya want for nothing?")) == "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843") "hmac 2"
  expect (hex (hmacSha256 (List.replicate 131 0xaa) (ascii "Test Using Larger Than Block-Size Key - Hash Key First")) ==
    "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54") "hmac 6 (key longer than a block)"
  -- C against the Lean model, every length around the block boundaries, and random bytes
  let mut s : Nat := 12345
  for n in List.range 200 do
    let mut b : Bytes := []
    for _ in List.range n do
      s := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
      b := (s / 2 ^ 33 % 256).toUInt8 :: b
    expect (sha256L b == sha256Model b) s!"sha256: C differs from the Lean model at length {n}"
  IO.println "ran: sha256 and hmac known answers; C against the Lean model on 200 inputs"

/-! ## The instrumented real table

Every effect of the driver goes to the real shim, then to a shadow of the model file (`Fs.run`), and the real file's bytes are compared with the
shadow's. A cut raises at the n-th file effect; the harness then makes the crash the model describes (the file keeps its durable bytes and `keep`
of the pending ones, or is gone). -/

structure Rig where
  path : String
  shadow : IO.Ref Fs
  sigShadow : IO.Ref (Option Bytes)
  cut : IO.Ref (Option Cut)
  count : IO.Ref Nat

def Rig.new (dir : String) (name : String) : IO Rig := do
  pure { path := dir ++ "/" ++ name, shadow := ← IO.mkRef Fs.empty, sigShadow := ← IO.mkRef none, cut := ← IO.mkRef none, count := ← IO.mkRef 0 }

def readReal (path : String) : IO Bytes := do pure ((← realReadFile path).map (·.toList) |>.getD [])

/-- Set the real file to the bytes (or remove it). -/
def setReal (path : String) (b : Option Bytes) : IO Unit := do
  match b with
  | none => if ← System.FilePath.pathExists path then IO.FS.removeFile path
  | some b => IO.FS.writeBinFile path b.toByteArray

def Rig.shims (r : Rig) : Shims RealM :=
  let real := Shims.real r.path
  let eff (e : Effect) (act : RealM Unit) : RealM Unit := do
    if let some c := ← r.cut.get then
      if (← r.count.get) = c.n then throw "CUT"
    act
    r.count.modify (· + 1)
    r.shadow.modify (·.run e)
    let want := (← r.shadow.get).contents
    let got ← readReal r.path
    if got != want then throw s!"DIFF: the file after {repr e} is not the model's"
  { real with
    write := fun b => eff (.write b) (real.write b)
    fsync := eff .fsync real.fsync
    fsyncDir := eff .fsyncDir real.fsyncDir
    truncate := fun n => eff (.truncate n) (real.truncate n)
    putSig := fun b => do
      real.putSig b
      r.sigShadow.set (some b)
      if (← liftShim (realReadFile (r.path ++ ".sig"))).map (·.toList) != some b then throw "DIFF: the signature file is not what was put" }

/-- The crash the model describes, applied to the real file. -/
def Rig.crash (r : Rig) (keep : Nat) (vanish : Bool) : IO Unit := do
  r.shadow.modify (·.crash keep vanish)
  let f ← r.shadow.get
  setReal r.path (if f == Fs.empty then none else some f.contents)

def isReady : Mode → Bool
  | .ready _ _ => true
  | _ => false

/-- One event of the system on the real files. -/
def Rig.event (P : Params) (r : Rig) (st : St) (ev : WEvent) : IO St := do
  let run (e : Event) (cut : Option Cut) : IO St := do
    r.cut.set cut
    r.count.set 0
    match ← (driveSigned P macK r.shims st e).run with
    | .error m => fail s!"unexpected error escaped the driver: {m}"; pure st
    | .ok (st', none) =>
      match cut with
      | some c =>
        if st' != st && isReady st'.mode then
          r.crash c.keep c.vanish
          pure (step P st' .crash).1
        else pure st'
      | none => pure st'
    | .ok (st', some "CUT") =>
      let c := (cut.getD ⟨0, 0, false⟩)
      r.crash c.keep c.vanish
      pure st'
    | .ok (_, some m) => fail s!"driver error: {m}"; pure st
  match ev with
  | .takeOver => run .takeOver none
  | .crash k v => r.crash k v; pure (step P st .crash).1
  | .recover g cut => run (.recover g) cut
  | .append g e cut => run (.append g e) cut

/-- Run a script on the real files and on the model; they must agree after every event (the machine state, the file's bytes, the model's `Fs`). -/
def differential (P : Params) (dir : String) (name : String) (evs : List WEvent) : IO Unit := do
  let r ← Rig.new dir name
  setReal r.path none
  setReal (r.path ++ ".sig") none
  let mut st := St.init
  let mut w := World.init
  let mut i := 0
  for ev in evs do
    i := i + 1
    st ← r.event P st ev
    w := w.step P ev
    expect (st == w.m) s!"{name}: event {i}: the machine state differs from the model"
    expect ((← readReal r.path) == w.fs.contents) s!"{name}: event {i}: the real file differs from the model file"
    expect ((← r.shadow.get) == w.fs) s!"{name}: event {i}: the effects differ from the model's"
    -- the signature never contradicts a journal that verifies: the reader accepts it (an unsigned tail is accepted)
    if (read P w.fs.contents).isSome then
      match ← (readSigned P macK (Shims.real r.path)).run with
      | .ok (rd, _) => expect (rd.entries == entriesOfRead P w.fs.contents) s!"{name}: event {i}: the reader's entries differ"
      | .error m => fail s!"{name}: event {i}: the reader refused a journal that verifies: {m}"
where
  entriesOfRead (P : Params) (b : Bytes) : List Entry := ((read P b).map (·.entries)).getD []

def goldenTests (dir : String) : IO Unit := do
  for (n, evs) in Examples.scripts do
    differential Examples.P dir s!"golden-{(n.replace " " "-")}" evs
  -- the tampered files: recovery on each, real against model
  for (n, b) in Examples.tamperFiles do
    let r ← Rig.new dir s!"tamper-{n}"
    setReal r.path (some b)
    setReal (r.path ++ ".sig") none
    r.shadow.set ⟨b, [], true⟩
    let st ← r.event Examples.P ⟨1, .opened⟩ (.recover 1 none)
    let w := World.step Examples.P ⟨⟨1, .opened⟩, ⟨b, [], true⟩⟩ (.recover 1 none)
    expect (st == w.m) s!"tamper {n}: the machine state differs from the model"
    expect ((← readReal r.path) == w.fs.contents) s!"tamper {n}: the real file differs from the model file"
  IO.println "ran: golden cases and tampered files, the driver over the real shims against the slice 1 model"

/-! ## Random scripts -/

def lcg (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

def randomScript (seed : Nat) (len : Nat) : List WEvent := Id.run do
  let mut s := seed
  let mut gen := 1
  let mut out : List WEvent := [.takeOver, .recover 1 none]
  for _ in List.range len do
    s := lcg s
    let a := s / 2 ^ 20
    s := lcg s
    let b := s / 2 ^ 20
    let cut : Option Cut := if b % 3 = 0 then some ⟨b / 3 % 5, b / 15 % 40, b / 600 % 2 = 0⟩ else none
    let g := if a % 5 = 0 then gen - 1 else gen
    let ev : WEvent :=
      match a % 16 with
      | 0 => .takeOver
      | 1 | 2 => .recover g cut
      | 3 => .crash (b % 30) (b / 30 % 2 = 0)
      | 4 | 5 => .append g (.call (b % 4)) cut
      | 6 | 7 => .append g (.done (b % 4) (b / 4 % 2 = 0)) cut
      | _ => .append g (.note (b % 6)) cut
    if a % 16 = 0 then gen := gen + 1
    out := out ++ [ev]
  return out

def randomTests (dir : String) : IO Unit := do
  for seed in List.range 400 do
    differential Params.real dir s!"random-{seed}" (randomScript (seed + 1) 20)
  IO.println "ran: random scripts with crashes, the driver over the real shims against the slice 1 model (SHA-256 chain)"

/-! ## The real crash test -/

/-- The i-th record of the crash test (small, so that recovery is quick). -/
def noteOf (i : Nat) : Nat := i % 7 + 1

def writer (path : String) : IO Unit := do
  let sh := Shims.real path
  let mut st := St.init
  let step1 (st : St) (ev : Event) : IO St := do
    match ← (driveSigned Params.real (macReal key) sh st ev).run with
    | .ok (st', none) => pure st'
    | _ => IO.eprintln "writer: failed"; IO.Process.exit 2
  st ← step1 st .takeOver
  st ← step1 st (.recover st.gen)
  let out ← IO.getStdout
  for i in List.range 1000000 do
    st ← step1 st (.append st.gen (.note (noteOf (i + 1))))
    out.putStrLn (toString (i + 1))   -- acknowledged: durable and signed
    out.flush

/-- After the kill: recover (take over, recover) and check that the journal holds the records 1..k in order, that k is at least what was acknowledged (and at most one more), and that the signature accepts it. -/
def verifyCrash (path acks : String) : IO Unit := do
  let sh := Shims.real path
  let acked := ((← IO.FS.readFile acks).splitOn "\n").dropLast.filterMap String.toNat? |>.foldl max 0
  let step1 (st : St) (ev : Event) : IO St := do
    match ← (driveSigned Params.real (macReal key) sh st ev).run with
    | .ok (st', none) => pure st'
    | .ok (_, some m) => fail s!"crash test: recovery failed: {m}"; pure st
    | .error m => fail s!"crash test: {m}"; pure st
  let mut st ← step1 St.init .takeOver
  st ← step1 st (.recover st.gen)
  match ← (readSigned Params.real (macReal key) sh).run with
  | .error m => fail s!"crash test: the recovered journal is refused: {m}"
  | .ok (r, v) =>
    let k := r.entries.length
    expect (r.entries == (List.range k).map fun i => Entry.note (noteOf (i + 1))) "crash test: the records are not the records 1..k in order"
    expect (acked ≤ k && k ≤ acked + 1) s!"crash test: {k} records, {acked} acknowledged"
    expect (v == .signed k 0) "crash test: the signature does not cover the recovered journal"
    IO.println s!"ran: crash test: killed after {acked} acknowledged appends; recovered {k} records ({r.tail.length} torn bytes were dropped at recovery)"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["writer", path] => writer path; pure 0
  | ["verify", path, acks] => verifyCrash path acks; pure 0
  | _ =>
    shaTests
    let dir ← IO.FS.createTempDir
    goldenTests dir.toString
    randomTests dir.toString
    IO.FS.removeDirAll dir
    pure 0
