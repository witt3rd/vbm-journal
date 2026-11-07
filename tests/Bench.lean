import VbmJournal
/-! A measurement, not a test (nothing gates on it): `vbm-journal-bench PATH MB` writes a synthetic journal of about MB megabytes (SHA-256 chain, signed head)
and times reading it: the file into a flat buffer, `readB` (the chain verified, the entries decoded), and `readSigned` (the reader as a host calls it:
file, chain and signature). Run it under the Lean toolchain (`mise exec -- .lake/build/bin/vbm-journal-bench /tmp/j.journal 50`). -/
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
  let [path, mb] := args | IO.eprintln "usage: vbm-journal-bench PATH MB"; return 2
  let want := mb.toNat! * 1000000
  let P := Params.real
  -- the journal: lines of about 190 bytes, built a line at a time and kept flat
  let t0 ← IO.monoMsNow
  let mut buf := ByteArray.empty
  let mut head := P.genesis
  let mut n := 0
  while buf.size < want do
    let e := Entry.note (100 + n % 40)
    buf := buf ++ (frame (lineOf P head e)).toByteArray
    head := P.link head (P.enc e)
    n := n + 1
  IO.println s!"built {n} records, {buf.size} bytes in {(← IO.monoMsNow) - t0} ms"
  IO.FS.writeFile path ""
  IO.FS.removeFile path
  realWrite path buf
  realReplace (path ++ ".sig") (Sig.make (macReal key) n head).toBytes.toByteArray
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
