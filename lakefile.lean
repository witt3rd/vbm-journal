import Lake
open System Lake DSL

package «vbm-journal» where
  leanOptions := #[⟨`warningAsError, true⟩, ⟨`autoImplicit, false⟩]

/-- The specification and the verified implementation: one Lean core, `Init` only (what is compiled to C and linked). -/
@[default_target]
lean_lib VbmJournal where
  globs := #[.andSubmodules `VbmJournal]

/-- The proofs: may import `Std` and `Lean`; never linked. Built by default, so that `lake build` checks them. -/
@[default_target]
lean_lib VbmJournalProofs where
  globs := #[.andSubmodules `VbmJournalProofs]

/-- The trusted C (docs/trust-ledger.md): the shims of the real driver, and nothing else. -/
target shimO pkg : FilePath := do
  let src ← inputTextFile (pkg.dir / "native" / "vbm_journal.c")
  buildO (pkg.buildDir / "native" / "vbm_journal.o") src #["-I", (← getLeanIncludeDir).toString]
    #["-std=c11", "-O2", "-fPIC", "-Wall", "-Wextra", "-Werror"] "cc"

extern_lib libvbmjournalshim pkg := do
  let o ← shimO.fetch
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "vbmjournalshim") #[o]

/-- The tests of Tier 1 (`tests/tier1.sh`): the shims against their models, the differential test of the driver over the real shims, the crash test. -/
@[default_target]
lean_exe «vbm-journal-test» where
  root := `Main
  srcDir := "tests"

/-- A measurement of reading a synthetic journal of megabytes (`tests/Bench.lean`): not run by Tier 1, nothing gates on it. -/
lean_exe «vbm-journal-bench» where
  root := `Bench
  srcDir := "tests"
