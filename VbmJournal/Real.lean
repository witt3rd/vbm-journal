import VbmJournal.Driver
/-! # vbm-journal slice 2, part 4: the real shims

The table of shims over the operating system: the `@[extern]` declarations are the **trusted C** (`native/vbm_journal.c`, one entry per shim in
docs/trust-ledger.md); their Lean models are `VbmJournal.Sim`, the file the proofs run the driver over. Each takes the path of the file it acts on
(the journal's, or its signature's: `<journal>.sig`) and opens and closes it, so no file descriptor is kept between effects. -/
namespace VbmJournal

/-- Shim `write`: append to the file, creating it (mode 0600) if there is none. -/
@[extern "vbm_write"] opaque realWrite (path : @& String) (bytes : @& ByteArray) : IO Unit
/-- Shim `fsync`: everything written to the file is durable. -/
@[extern "vbm_fsync"] opaque realFsync (path : @& String) : IO Unit
/-- Shim `fsyncDir`: the file's directory entry is durable. -/
@[extern "vbm_fsync_dir"] opaque realFsyncDir (path : @& String) : IO Unit
/-- Shim `truncate`: cut the file back to `len` bytes, durably. -/
@[extern "vbm_truncate"] opaque realTruncate (path : @& String) (len : UInt64) : IO Unit
/-- Shim `readFile`: the whole file, or `none` when there is none. -/
@[extern "vbm_read_file"] opaque realReadFile (path : @& String) : IO (Option ByteArray)
/-- Shim `replace`: the file becomes exactly these bytes, all or nothing, durably. -/
@[extern "vbm_replace"] opaque realReplace (path : @& String) (bytes : @& ByteArray) : IO Unit

/-- The monad of the real driver: `IO`, whose errors are messages. -/
abbrev RealM := ExceptT String IO

/-- Run an `IO` shim; its error becomes the message. -/
def liftShim {α : Type} (x : IO α) : RealM α :=
  ExceptT.mk (do try pure (Except.ok (← x)) catch e => pure (Except.error (toString e)))

/-- **The real table**, for the journal at `path` (its signature is `path ++ ".sig"`). -/
def Shims.real (path : String) : Shims RealM where
  write b := liftShim (realWrite path b.toByteArray)
  fsync := liftShim (realFsync path)
  fsyncDir := liftShim (realFsyncDir path)
  readAll := do pure ((← liftShim (realReadFile path)).getD ByteArray.empty)
  truncate n := liftShim (realTruncate path n.toUInt64)
  putSig b := liftShim (realReplace (path ++ ".sig") b.toByteArray)
  getSig := do pure ((← liftShim (realReadFile (path ++ ".sig"))).map (·.toList))

/-- Hash input of a chain link: the previous digest in a prefix code (every byte after a one, the end after a zero), then the body. It cannot be
read two ways, whatever the digest is, so a collision of the hash is the only way for two links to agree (`VbmJournalProofs.Real`). -/
def chainInput (p b : Bytes) : Bytes := p.flatMap (fun x => [1, x]) ++ 0 :: b

/-- `chainInput` with the body flat: the prefix-coded digest is short (a few dozen bytes), the body is not copied into a list. -/
def chainInputB (p : Bytes) (b : ByteArray) : ByteArray := (p.flatMap (fun x => [1, x]) ++ [0]).toByteArray ++ b

theorem chainInputB_eq (p : Bytes) (b : ByteArray) : chainInputB p b = (chainInput p b.toList).toByteArray := by
  have : chainInput p b.toList = (p.flatMap (fun x => [1, x]) ++ [0]) ++ b.toList := by simp [chainInput]
  rw [this, List.toByteArray_append, toByteArray_toList]
  rfl

/-- **The real parameters**: the chain is SHA-256 (`link p b` is the hex of the hash of `chainInput p b`; the genesis the hex of the hash of a
label), the codec the unary one (lung's JSON codec is slice 3's). -/
def Params.real : Params where
  genesis := hexOf (sha256L (ascii "vbm-journal-v1"))
  link p b := hexOf (sha256L (chainInput p b))
  enc := encUnary
  dec := decUnary
  linkB p b := hexOf (sha256 (chainInputB p b)).toList
  decB b := decUnary b.toList
  linkB_eq p b := by simp only [chainInputB_eq, sha256L]
  decB_eq _ := rfl

end VbmJournal
