import Lean
import VbmJournalProofs.Theorems
import VbmJournalProofs.Witness
import VbmJournalProofs.SigImpl
import VbmJournalProofs.Real
import VbmJournalProofs.SigWorld
/-! # The theorems rest on the standard axioms only

Every theorem of slice 1 listed here uses no axiom beyond `propext`, `Classical.choice` and `Quot.sound` (no `sorryAx`, no axiom of
our own). The build fails if one does. -/
open Lean Elab Command

run_cmd do
  let standard : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let theorems : List Name := [
    -- (a) append-only
    ``VbmJournal.inv_step, ``VbmJournal.append_only, ``VbmJournal.append_only_reachable, ``VbmJournal.reachable_inv,
    -- (b) chain integrity
    ``VbmJournal.read_encode, ``VbmJournal.reachable_verifies, ``VbmJournal.head_binds, ``VbmJournal.headFrom_inj,
    ``VbmJournal.verify_only_prefix, ``VbmJournal.perm_verifies_only_if_same, ``VbmJournal.edit_fails,
    ``VbmJournal.anchored_unique, ``VbmJournal.anchored_short_fails, ``VbmJournal.anchored_honest,
    -- (c) crash consistency
    ``VbmJournal.crash_consistency, ``VbmJournal.crash_before_effects, ``VbmJournal.crash_after_plan,
    ``VbmJournal.recovered_after_crash,
    -- (d) fencing
    ``VbmJournal.stale_refused, ``VbmJournal.takeOver_fences, ``VbmJournal.world_takeOver_fences,
    ``VbmJournal.live_unique, ``VbmJournal.accepted_is_live, ``VbmJournal.gen_mono,
    -- (e) recovery
    ``VbmJournal.reopen_settles, ``VbmJournal.reopen_idempotent, ``VbmJournal.reopen_crash_safe,
    ``VbmJournal.settle_once, ``VbmJournal.settle_closes, ``VbmJournal.settle_idem, ``VbmJournal.settle_partial,
    -- the implementation is the model (slice 2)
    ``VbmJournal.runPlan_nocut, ``VbmJournal.runPlan_cut, ``VbmJournal.drive_planned, ``VbmJournal.drive_recover,
    ``VbmJournal.impl_step_eq, ``VbmJournal.impl_run_eq, ``VbmJournal.impl_reachable,
    ``VbmJournal.impl_append_only, ``VbmJournal.impl_verifies, ``VbmJournal.impl_crash_consistency, ``VbmJournal.impl_reopen_idempotent,
    ``VbmJournal.impl_reopen_settles, ``VbmJournal.impl_stale_append, ``VbmJournal.impl_stale_recover, ``VbmJournal.impl_takeOver_fences,
    -- the signed head
    ``VbmJournal.sig_roundtrip, ``VbmJournal.parseDec_natDec, ``VbmJournal.verdict_none, ``VbmJournal.verdict_unreadable,
    ``VbmJournal.verdict_bad_mac, ``VbmJournal.verdict_cut_back, ``VbmJournal.verdict_rewritten, ``VbmJournal.verdict_signed,
    ``VbmJournal.verdict_sound, ``VbmJournal.verdict_unsigned_only, ``VbmJournal.verdict_honest, ``VbmJournal.verdict_anchored,
    ``VbmJournal.signed_unique, ``VbmJournal.signed_append_ok, ``VbmJournal.signed_append_verifies, ``VbmJournal.signed_append_fault,
    ``VbmJournal.signed_recover_refused, ``VbmJournal.signed_recover_ok, ``VbmJournal.signed_recover_verifies,
    ``VbmJournal.honest_mono, ``VbmJournal.honest_gate, ``VbmJournal.signed_step, ``VbmJournal.signed_reachable,
    ``VbmJournal.signed_reachable_verifies,
    -- the real parameters
    ``VbmJournal.real_lawful, ``VbmJournal.hexOf_inj, ``VbmJournal.chainInput_inj,
    -- the laws are satisfiable
    ``VbmJournal.sym_lawful, ``VbmJournal.decUnary_encUnary, ``VbmJournal.encUnary_decUnary]
  for n in theorems do
    let axs ← liftCoreM <| collectAxioms n
    for a in axs do
      unless standard.contains a do
        throwError "{n} depends on the axiom {a}"
