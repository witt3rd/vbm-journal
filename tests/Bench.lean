import VbmJournal
/-! A measurement, not a test (nothing gates on it): `vbm-journal-bench PATH MB (plain|jsonl)` writes a synthetic journal of about MB megabytes (SHA-256 chain, signed head), in the plain format or the JSON-lines format
and times reading it: the file into a flat buffer, `readB` (the chain verified, the entries decoded), and `readSigned` (the reader as a host calls it:
file, chain and signature). Run it under the Lean toolchain (`mise exec -- .lake/build/bin/vbm-journal-bench /tmp/j.journal 50 jsonl`). -/
open VbmJournal

def key : Bytes := ascii "bench-key"

def peakKb : IO String := do
  let s ← IO.FS.readFile "/proc/self/status"
  pure ((s.splitOn "\n").filter (·.startsWith "VmHWM") |>.headD "")

def timed {α : Type} (what : String) (act : IO α) : IO α := do
  let t0 ← IO.monoMsNow
  let r ← act
  IO.println s!"{what}: {(← IO.monoMsNow) - t0} ms"
  pure r

def main (args : List String) : IO UInt32 := do
  let [path, mb, fmt] := args | IO.eprintln "usage: vbm-journal-bench PATH MB (plain|jsonl)"; return 2
  let want := mb.toNat! * 1000000
  let P := if fmt == "jsonl" then Params.jsonl (ascii "bench-journal-v1") else Params.real
  -- a record: unary `note` for the plain format, a host record (a JSON object of about 190 bytes) for the JSON lines
  let entry (n : Nat) : Entry :=
    if fmt == "jsonl" then
      let b := (ascii s!"\{\"h\":{n},\"k\":\"put\",\"t\":\"{String.ofList (List.replicate 150 'x')}\"}").toByteArray
      if h : bodyWf b.toList = true then .body ⟨b, h⟩ else .note 0
    else .note (100 + n % 40)
  -- the journal: lines of about 190 bytes, built a line at a time and kept flat
  let t0 ← IO.monoMsNow
  let mut buf := ByteArray.empty
  let mut head := P.genesis
  let mut n := 0
  while buf.size < want do
    let e := entry n
    buf := buf ++ (frame (lineOf P head e)).toByteArray
    head := P.link head (P.enc e)
    n := n + 1
  IO.println s!"built {n} records, {buf.size} bytes in {(← IO.monoMsNow) - t0} ms"
  IO.FS.writeFile path ""
  IO.FS.removeFile path
  realWrite path buf
  realReplace (path ++ ".sig") (P.sigEnc (Sig.make (macReal key) n head)).toByteArray
  IO.println (← peakKb)
  let sh := Shims.real path
  let b ← timed "read the file into a flat buffer" (do pure ((← realReadFile path).getD ByteArray.empty))
  let r ← timed "readB (verify the chain, decode every entry)" (IO.lazyPure fun _ => readB P b)
  match r with
  | none => IO.eprintln "FAILED: the journal does not verify"; return 1
  | some rd =>
    IO.println s!"  {rd.entries.length} entries, head ok: {rd.head == head}"
    IO.println (← peakKb)
    let v ← timed "readSigned (file, chain, signature verdict)" (do pure (← (readSigned P (macReal key) sh).run))
    match v with
    | .ok (rd2, vd) => IO.println s!"  {rd2.entries.length} entries, verdict {repr vd}"
    | .error e => IO.eprintln s!"FAILED: {e}"; return 1
    IO.println (← peakKb)
    return 0
