# The Lean gates

For a repository that has `.land/lean.conf` (the presence of the file is the opt-in; docs/payload.md 1a and 4a). The tool owns HOW a gate checks (`lean/`, vendored in `.land/tool/lean/`); the repository's file says WHICH modules. Run from the repository root: `.land/tool/bin/land-lean axiom [--selftest]`, `recheck [--selftest]`, `trust [--count]`. A Lean toolchain is on the PATH (the repository's `mise.toml`).

## `.land/lean.conf`

Same grammar as `land.conf` and the same parser (`lib/conf.sh`): `LAND_KEY=value` lines, `#` comments, an optional pair of quotes, nothing expanded or run, an unknown key is an error. Its own keys:

| key | meaning |
|---|---|
| `LAND_LEAN_AXIOM_IMPORTS` | the modules to import, space separated (dotted names allowed) |
| `LAND_LEAN_AXIOM_ROOTS` | the module roots whose constants are audited, space separated |
| `LAND_LEAN_RECHECK_MODULES` | the modules whose proofs the checker replays, space separated (each replays its whole import closure: usually the top module of each library) |
| `LAND_LEAN_TRUST_FILES` | path patterns of the trusted files beyond the build pins (C files, binding loaders, CI workflows), e.g. `native/*.c` |
| `LAND_LEAN_TRUST_EXTERN_DIRS` | the directories scanned for `@[extern]` declarations |
| `LAND_LEAN_TRUST_TOOLS` | the tools whose use by the scripts the ledger must name (default `git gh mise lake leanc`) |
| `LAND_LEAN_TRUST_KEYS_CMD` | a command printing more required keys, one per line: what the tool cannot derive (for instance closure modules); run with `bash -c` from the repository root |

Module lists hold module names only, path lists path patterns only, the tool list tool names only. `land-check` validates the file like `land.conf` (a typo is drift, not a silently disabled gate).

```
# a library with a pinned dependency (vbm-json)
LAND_LEAN_AXIOM_IMPORTS="LeanJson LeanJsonProofs LeanJsonSimd.ParseSimd"
LAND_LEAN_AXIOM_ROOTS="LeanJson LeanJsonProofs LeanJsonSimd VbmSimd VbmSimdProofs"
```

## `land-lean axiom`

Every constant defined in a module of the audited roots may depend only on `propext`, `Classical.choice` and `Quot.sound`; otherwise it exits 1 and names each offender. One shared walk over the union of the closures finds them in linear time. A root that matches no constant is an error (exit 1): a gate that audited nothing proves nothing.

`--selftest` also runs the differential test: the shared walk must give, constant by constant, the same axiom set as Lean's own `collectAxioms` (on a sample of the real constants, all of them with `AXIOM_DIFF_FULL=1`) and on planted axioms of every kind of constant (an axiom, definition, theorem, opaque, inductive, its constructor and recursor, a definition through the quotient constants, each also behind chains of depth 1 and 5), and it must catch deliberately broken walks. Run it once in the fast gate; it takes seconds on a small library.

Exit codes: 0 ok, 1 the gate failed, 2 usage or a refused configuration.

## `land-lean recheck [--selftest]`

Replays every proof of the modules in `LAND_LEAN_RECHECK_MODULES`, and of everything they import (the vendored libraries and Lean's own core included), with Lean's own checker, `leanchecker --fresh`: every declaration goes through the kernel again, in a fresh process, from the compiled files. What it catches: a declaration that reached the environment without passing the kernel (the check skipped, an option or tactic that bypasses it) and an `.olean` that an honest build did not produce. What it does NOT catch: a bug in the kernel itself, which it shares with the build; that needs a different implementation (nanoda). It reads no source: it replays the compiled proofs. Measured on the largest consumer (a 22,000-constant closure): about 2 minutes for one run on the top module, which covers the whole closure; run it in the background beside the tests.

`--selftest` is the gate's own negative test: it compiles a true theorem and a FALSE one added straight to the environment with the kernel check skipped (a declaration that bypassed the kernel), and requires the checker to accept the first and reject the second. A checker that accepts everything fails it. `LEANCHECKER` names another checker (a test seam). `leanchecker --fresh` takes one module per run, so each listed module is replayed on its own, side by side, with one verdict per module. Exit 0 ok, 1 a proof was rejected or a module is missing, 2 refused configuration. The nanoda checker (a second, independent implementation, the one that would catch a kernel bug) is not wired here: it needs an export step and its own pin, and is its own issue.

## The trust ledger: `land-lean trust [--count]`

The discipline: **what cannot be proven is marked as trusted.** A repository keeps one `docs/trust-ledger.md` naming everything it relies on without proof (the compiler, the runtime, a C file, an FFI symbol, a vendored library, a tool); a claim not yet proved sits in `docs/obligations.md` as `open` or `partial`, never silently. Every formally verified repository has one: even a pure-Lean library trusts the Lean kernel, compiler and runtime. A repository that proves nothing and generates no code (this tool, the hub) has no claims to qualify and keeps none: a ledger marks the limits of a proof.

Each entry is `### T<n>. <title>` with the fields `What`, `Enters` (where it enters the tree), `Assumes` (the contract, a path in the repository, or `no written contract`), `Test` (a path to a test that can fail, or `none`), `Owner`, `Plan` (starts with `verify`, `replace`, `sandbox` or `accept`; `accept` needs `because ...`) and `Covers` (the keys it accounts for, in backticks).

**Completeness is derived from the tree, never from the ledger**, so a definition cannot be relabelled out of the ledger. The tool derives the keys every ledger must cover:

| key | derived from |
|---|---|
| `file:PATH` | the build pins that exist (`lean-toolchain`, `mise.toml`, `lakefile.lean`, `lakefile.toml`) and every file matching `LAND_LEAN_TRUST_FILES` |
| `lean-compiler`, `lean-runtime`, `clang-lld` | a `lean-toolchain` exists |
| `extern:SYMBOL` | every `@[extern]` in `LAND_LEAN_TRUST_EXTERN_DIRS` (`extern:UNNAMED` for one with no symbol) |
| `pin:NAME` | every line of `.land/pins.lock`: a vendored library is a ledger line, and a repository claims no better than it does |
| `dep:NAME/include/F.h`, `extern:SYMBOL` | each vendored library's own `include/*.h` (its published surface) and its `@[extern]` symbols, at any depth (a library vendored inside a vendored library runs in our artifacts too); a header elsewhere in a library (a `runtime/include/` of its own) is not required |
| `tool:NAME` | `python3` always (the checker runs in it), and each tool in `LAND_LEAN_TRUST_TOOLS` the scripts or the build file mention |
| anything else | the output of `LAND_LEAN_TRUST_KEYS_CMD` |

The checker fails when a required key is not covered, when a `Covers` token names nothing required (a stale entry), when an entry is incomplete, or when a file an entry cites does not exist. It negative-tests itself on every run: removing any one entry must fail it.

Exit codes as for the other gates. It prints `trust ledger: N entries (...)`; `--count` prints only N and needs no build.
