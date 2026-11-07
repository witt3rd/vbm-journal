import VbmJournal.Concrete
/-! # vbm-journal slice 2, part 1: SHA-256 and HMAC-SHA256, the digest shim

The digest of the chain and the mac of the signature are SHA-256 and HMAC-SHA256. **SHA-256 is the one trusted hash**: `sha256` is an
`@[extern]` declaration whose C code (`native/vbm_journal.c`) is trusted (docs/trust-ledger.md, shim `sha256`), and whose Lean body, `sha256Model`,
is the FIPS 180-4 algorithm written out in Lean. The body is what the kernel sees; the compiled code calls C. The differential test runs the two
against each other (known answers and random inputs). HMAC (RFC 2104) is **not** a shim: it is defined here over `sha256`, so it adds nothing to the
trusted code. The proofs take the collision resistance of `sha256` as a hypothesis (`VbmJournalProofs.Real`); nothing here proves it. -/
namespace VbmJournal

namespace Sha

/-- The round constants. -/
def K : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- The initial hash value. -/
def H0 : Array UInt32 := #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

def rotr (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

/-- The message schedule of one 64-byte block. -/
def schedule (blk : Array UInt8) : Array UInt32 := Id.run do
  let mut w : Array UInt32 := Array.replicate 64 0
  for i in [0:16] do
    let b (j : Nat) : UInt32 := (blk[4 * i + j]!).toUInt32
    w := w.set! i ((b 0 <<< 24) ||| (b 1 <<< 16) ||| (b 2 <<< 8) ||| b 3)
  for i in [16:64] do
    let x := w[i - 15]!
    let y := w[i - 2]!
    let s0 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
    let s1 := rotr y 17 ^^^ rotr y 19 ^^^ (y >>> 10)
    w := w.set! i (w[i - 16]! + s0 + w[i - 7]! + s1)
  return w

/-- One compression: the hash value after a block. -/
def compress (h : Array UInt32) (blk : Array UInt8) : Array UInt32 := Id.run do
  let w := schedule blk
  let mut a := h[0]!
  let mut b := h[1]!
  let mut c := h[2]!
  let mut d := h[3]!
  let mut e := h[4]!
  let mut f := h[5]!
  let mut g := h[6]!
  let mut hh := h[7]!
  for i in [0:64] do
    let s1 := rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25
    let ch := (e &&& f) ^^^ ((~~~e) &&& g)
    let t1 := hh + s1 + ch + K[i]! + w[i]!
    let s0 := rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22
    let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let t2 := s0 + maj
    hh := g
    g := f
    f := e
    e := d + t1
    d := c
    c := b
    b := a
    a := t1 + t2
  return #[h[0]! + a, h[1]! + b, h[2]! + c, h[3]! + d, h[4]! + e, h[5]! + f, h[6]! + g, h[7]! + hh]

/-- The message, padded: a one bit, zeros, and the bit length as 8 big-endian bytes, to a multiple of 64 bytes. -/
def pad (msg : Bytes) : Bytes :=
  let n := msg.length
  let zeros := (119 - n % 64) % 64
  let bits := n * 8
  msg ++ [0x80] ++ List.replicate zeros 0 ++ (List.range 8).reverse.map fun i => (bits / 256 ^ i % 256).toUInt8

/-- The blocks of a padded message: `fuel` is at least the number of blocks. -/
def blocks : Nat → Bytes → List (Array UInt8)
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, l => (l.take 64).toArray :: blocks fuel (l.drop 64)

def words (h : Array UInt32) : Bytes :=
  h.toList.flatMap fun (x : UInt32) => [(x >>> 24).toUInt8, (x >>> 16).toUInt8, (x >>> 8).toUInt8, x.toUInt8]

end Sha

/-- SHA-256 in Lean (FIPS 180-4): the model of the shim `sha256`, and its executable specification. -/
def sha256Model (msg : Bytes) : Bytes :=
  let p := Sha.pad msg
  Sha.words ((Sha.blocks (p.length / 64 + 1) p).foldl Sha.compress Sha.H0)

/-- **The shim `sha256`**: the compiled code is C (`vbm_sha256`); the kernel sees `sha256Model`. -/
@[extern "vbm_sha256"]
def sha256 (b : @& ByteArray) : ByteArray := (sha256Model b.toList).toByteArray

/-- The shim on lists of bytes. -/
def sha256L (b : Bytes) : Bytes := (sha256 b.toByteArray).toList

/-- Lower-case hex of bytes. -/
def hexOf (b : Bytes) : Bytes := b.flatMap fun x => [hexDigit (x.toNat / 16), hexDigit (x.toNat % 16)]

/-- HMAC (RFC 2104) over a hash `H` with block size 64. -/
def hmacWith (H : Bytes → Bytes) (key msg : Bytes) : Bytes :=
  let k0 := if key.length > 64 then H key else key
  let k := k0 ++ List.replicate (64 - k0.length) 0
  H (k.map (· ^^^ 0x5c) ++ H (k.map (· ^^^ 0x36) ++ msg))

/-- HMAC-SHA256: not a shim, defined over the shim `sha256`. -/
def hmacSha256 (key msg : Bytes) : Bytes := hmacWith sha256L key msg

end VbmJournal
