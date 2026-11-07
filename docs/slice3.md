# Slice 3: a host's journal, in megabytes, with the proofs intact

Slice 2 left three things between the library and a host that keeps its journal as JSON lines (`docs/slice2.md`, "What slice 3 must change"): the journal was read as a list of bytes, the line and the signature file were fixed plain-text formats, and the entry was the library's three. All three are done, and the trusted C is unchanged (`native/vbm_journal.c`, `docs/trust-ledger.md`).

## 1. Bytes: the compiled reader works on a flat buffer

The proofs keep their list shape (`Bytes` is `List UInt8`); the compiled code reads the file as a `ByteArray` and scans it by index, in a loop (`readB`, `verifyB`: `Basic`; `findByte`, `splitSpB`: `Scan`). It never makes a list of the file's bytes and never recurses once per line (slice 2 overflowed the stack at 20 MB).

| | Theorem | Module |
|---|---|---|
| **the flat reader is the list reader** | `readB_eq`: `readB P b = read P b.toList`, for every `Params`: same entries, same head, same torn tail, or the same refusal; `verifyB_eq` (its loop) | `Flat` |
| the machine | `recoverPlanB_eq`, `stepReplyB_eq`: the machine's step on the reply of a read, the bytes flat, is its step on the list | `Flat` |
| the formats' flat forms | `Params.linkB_eq`, `decB_eq`, `splitB_eq` are fields of `Params`: the flat digest, codec and line cut are proved equal to the list ones for every `Params` | `Basic`, `Json` |
| the buffer is its list | `toList_eq`, `toList_toByteArray`, `toByteArray_toList`, `toList_extract` | `Bytes` |

The driver reads with `readB` and the machine takes the bytes flat (`Shims.readAll : m ByteArray`); every theorem of slices 1 and 2 transfers through the equation, unchanged (`Impl`, `SigImpl`, `SigWorld` rewrite with `stepReplyB_eq`, `readB_eq` and the round trip of a list through a buffer). The model's own files (`Fs`, `Cut`, the plans) are still lists: the effects `write` and `truncate` carry the bytes of a line or a settlement, not of the file.

**Measured** (`tests/Bench.lean`, `vbm-journal-bench PATH MB (plain|jsonl)`; nothing gates on it; x86_64, one core): a synthetic signed journal of 50 MB, 199,646 records of about 250 bytes each, JSON lines.

| | time | peak memory |
|---|---|---|
| read the file | 25 ms | |
| `readB` (verify the whole chain, keep every record) | 2.6 s | 145 MB |
| `readSigned` (file, chain, signature verdict) | 5.0 s | 209 MB |

Slice 2's list reader on the same kind of journal (plain format, `note` records): 1 MB, 0.27 s and 116 MB; 5 MB, 1.3 s and 524 MB; 20 MB, a stack overflow. Where the 2.6 s goes: SHA-256 in C is 0.7 s; the rest is the per-record work on the 64-byte digests, which the model keeps as lists. `readSigned` hashes the chain a second time to check the signature (the model's `verdict` recomputes the head at the signed index); a recovery reads the file twice (the gate, then the machine) and does that once more.

## 2. The line, the signature file and the host's record are parameters

`Params` now carries, besides the digest and the codec, the **line** (`frameLine`, `splitLine`) and the **signature file** (`sigEnc`, `sigDec`), and the laws the theorems need of them in `Params.Lawful`: `line_clean`, `split_line`, `split_inv` (a line is cut back into the digest and body that made it, and only those) and `sig_round` (what is signed is read back). The plain-text formats of slices 1 and 2 are the default (`Params.ofLists`) and meet the laws (`space_laws`).

**`Entry.body`**: a record of the host's own, a flat `ByteArray` (`Body`: a JSON object that begins with a key, has no newline and does not begin with the key `vbm`). The library chains, verifies, recovers and signs it without reading it; the host maps its records onto `body` (their compact JSON) and back. This is the deviation from "make `Entry` a parameter": the entry stays the closed type of slice 1 plus `body`, so that every theorem stays about one type; a host with no `call`/`done` records has nothing in flight and recovery adds nothing to its journal (`openCalls` ignores `body`). `edit_fails` is now stated of any line that cuts into the digest of the record it replaces (it implies the old statement).

**`Params.jsonl label`** (`Json`): the format of a host that keeps JSON lines with a digest chain.

* The line is `{"c":"<hex>",<the rest of the record>}`; the digest of a record is the hex of `SHA-256(prev "\n" body)`, `prev` the digest of the record before (hex text, then a newline) and `body` the record's compact JSON without the `c` key. The library never parses JSON: it cuts the digest out by position.
* The genesis is the hex of `SHA-256(label)`; the label is the host's.
* The signature file is `{"head":"<hex>","index":<n>,"mac":"<hex>"}`, the mac the hex of HMAC-SHA256 of `index:head` under the host's key (`macReal`, unchanged).
* The library's own entries are written as `{"vbm":"<unary code>"}`, so that every `Entry` has a line (the tests exercise the driver on them).
* A line is accepted only in exactly the form the writer makes (digest first, no whitespace); anything else is refused (fail closed).

| | Theorem | Module |
|---|---|---|
| **the JSON-lines parameters meet the laws** | `jsonl_lawful`: all of `Params.Lawful`, **if SHA-256 is collision resistant** and the label has no newline and does not begin with the byte 255 (as slice 2's `real_lawful`) | `Json` (proofs) |
| the digest binds for every input | `jInput_inj`: a hash input is `prev "\n" body` with `prev` a digest without a newline, so (`prev`, `body`) is the two sides of its first newline; a `prev` with a newline (no digest of a journal has one: they are hex) is hashed in an encoding with no newline, so `link_binds` holds for every input, not only the digests that occur | `Json` (proofs) |
| the codec | `jDec_jEnc` (round trip), `jEnc_jDec` (canonical), `jEnc_clean` | `Json` (proofs) |
| the line and the signature file | `jSplit_jFrame`, `jSplit_inv`, `jSig_round` | `Json` (proofs) |
| the flat forms | `jSplitB_eq`, `jDecB_eq`, `jLinkB_eq` | `Json` |

All theorems of slices 1 and 2 are kept; `Axioms.lean` fails the build if any uses an axiom beyond `propext`, `Classical.choice`, `Quot.sound`; there is no `sorry`.

## What is assumed, and what is not

* Everything of slice 2 (`docs/slice2.md`): the shims do what their models do; SHA-256 is collision resistant (now also the hypothesis of `jsonl_lawful`); HMAC-SHA256 is a MAC; a plan runs to its end or to a crash before the next event.
* **The host writes the body canonically.** A host's reader that re-serialises what it parsed (sorted keys, compact) hashes the re-serialisation; the library hashes the bytes of the line. A journal verifies under both exactly when the bytes are the canonical form, which a host's own writer always makes. A line the host's reader would accept that is not in that form (other key order, whitespace) is refused by the library, not reinterpreted. The library does not check that a body is JSON, or UTF-8.
* **The cross-process lock and the key are the host's** (slice 2): not in this library.
* **Recovery re-signs.** After recovering a journal with records, the driver signs the head (as after every change); a host that does not re-sign on open ends up with the same signature bytes when the journal had no unsigned tail, and a fresh one when it had.
* Speed is measured, not proved, and not a gate.

## Tests (Tier 1: `mise exec -- tests/tier1.sh`)

As slice 2, plus `jsonlTests` in `tests/Main.lean`: known lines, head and signature file made by an independent program (Python's `hashlib` and `hmac`), the flat reader against the list reader, torn tails of every length, fail-closed cases (an edited body or digest, whitespace, a digest that is not first, an empty line, swapped and deleted records), every kind of entry through the codec, and 150 random scripts with crashes: the driver over the real shims against the model, host records among the entries. The measurement is `vbm-journal-bench`, run by hand.
