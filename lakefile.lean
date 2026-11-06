import Lake
open System Lake DSL

package «vbm-journal» where
  leanOptions := #[⟨`warningAsError, true⟩, ⟨`autoImplicit, false⟩]

/-- The specification and the verified implementation: one Lean core, `Init` only (what is compiled to C and linked). -/
@[default_target]
lean_lib VbmJournal where
  globs := #[.andSubmodules `VbmJournal]

/-- The proofs: may import `Std` and `Lean`; never linked. -/
lean_lib VbmJournalProofs where
  globs := #[.andSubmodules `VbmJournalProofs]
