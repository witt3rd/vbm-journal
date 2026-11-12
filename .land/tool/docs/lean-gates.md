# The Lean gates

For a repository that has `.land/lean.conf` (the presence of the file is the opt-in; docs/payload.md 1a and 4a). The tool owns HOW a gate checks (`lean/`, vendored in `.land/tool/lean/`); the repository's file says WHICH modules. Run from the repository root: `.land/tool/bin/land-lean axiom [--selftest]`. A Lean toolchain is on the PATH (the repository's `mise.toml`).

## `.land/lean.conf`

Same grammar as `land.conf` and the same parser (`lib/conf.sh`): `LAND_KEY=value` lines, `#` comments, an optional pair of quotes, nothing expanded or run, an unknown key is an error. Its own keys:

| key | meaning |
|---|---|
| `LAND_LEAN_AXIOM_IMPORTS` | the modules to import, space separated (dotted names allowed) |
| `LAND_LEAN_AXIOM_ROOTS` | the module roots whose constants are audited, space separated |

Module lists hold module names only. `land-check` validates the file like `land.conf` (a typo is drift, not a silently disabled gate).

```
# a library with a pinned dependency (vbm-json)
LAND_LEAN_AXIOM_IMPORTS="LeanJson LeanJsonProofs LeanJsonSimd.ParseSimd"
LAND_LEAN_AXIOM_ROOTS="LeanJson LeanJsonProofs LeanJsonSimd VbmSimd VbmSimdProofs"
```

## `land-lean axiom`

Every constant defined in a module of the audited roots may depend only on `propext`, `Classical.choice` and `Quot.sound`; otherwise it exits 1 and names each offender. One shared walk over the union of the closures finds them in linear time. A root that matches no constant is an error (exit 1): a gate that audited nothing proves nothing.

`--selftest` also runs the differential test: the shared walk must give, constant by constant, the same axiom set as Lean's own `collectAxioms` (on a sample of the real constants, all of them with `AXIOM_DIFF_FULL=1`) and on planted axioms of every kind of constant (an axiom, definition, theorem, opaque, inductive, its constructor and recursor, a definition through the quotient constants, each also behind chains of depth 1 and 5), and it must catch deliberately broken walks. Run it once in the fast gate; it takes seconds on a small library.

Exit codes: 0 ok, 1 the gate failed, 2 usage or a refused configuration.
