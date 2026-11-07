import VbmJournalProofs.World
import VbmJournalProofs.Settle
/-! # What recovery does, exactly

`recover_spec` computes a completed recovery; `recover_cut_spec` computes one the crash cut. Theorem (e) and the recovery half of
crash consistency are read off them in `VbmJournalProofs.Theorems`. -/
set_option linter.unusedSectionVars false

namespace VbmJournal

variable {P : Params} {w : World}

section Lawful
variable (L : P.Lawful)
include L

/-- **A completed recovery**, computed. The file ends as the verified entries followed by their settlement, the writer is ready at that
head and count, nothing is pending, and the directory entry is durable unless there was no file at all. -/
theorem recover_spec (hI : Inv P w) (hm : w.m.mode = .opened) :
    ∃ r, read P w.fs.contents = some r ∧
      (w.step P (.recover w.m.gen none)).m = ⟨w.m.gen, .ready (headFrom P P.genesis (r.entries ++ settleEntries r.entries))
        (r.entries ++ settleEntries r.entries).length⟩ ∧
      (w.step P (.recover w.m.gen none)).fs.pending = [] ∧
      (w.step P (.recover w.m.gen none)).fs.contents = encodeFrom P P.genesis (r.entries ++ settleEntries r.entries) ∧
      (w.fs.contents ≠ [] → (w.step P (.recover w.m.gen none)).fs.dirSafe = true) ∧
      (w.fs.contents = [] → (w.step P (.recover w.m.gen none)).fs = w.fs) := by
  rw [step_recover_opened w hm]
  by_cases hE : w.fs.contents = []
  · have hread0 : read P w.fs.contents = some ⟨[], P.genesis, []⟩ := by rw [hE]; exact read_empty
    refine ⟨⟨[], P.genesis, []⟩, hread0, ?_⟩
    simp only [recoverPlan, hE, read_empty, ite_true, Mode.isBusy]
    rw [finish_none, acked_busy]
    simp only [Fs.runAll, List.foldl_nil]
    have hs : settleEntries [] = [] := rfl
    simp only [hs, List.append_nil, List.length_nil, headFrom, encodeFrom]
    simp [hI.pending, hE]
  · obtain ⟨r, hrd⟩ := hI.readable
    obtain ⟨hd, hnl, hh⟩ := read_inv L _ r hrd
    have hdur : w.fs.durable = encodeFrom P P.genesis r.entries ++ r.tail := by
      rw [← contents_of_pending_nil hI.pending]; exact hd
    have hgood : w.fs.contents.length - r.tail.length = (encodeFrom P P.genesis r.entries).length := by
      rw [hd]; simp
    refine ⟨r, hrd, ?_⟩
    simp only [recoverPlan, hrd, hE, ite_false, ite_true, Mode.isBusy, hh, hgood, ne_eq, not_false_eq_true]
    rw [finish_none, acked_busy]
    have hfull := full_run (P := P) w.fs hI.pending r.entries (settleEntries r.entries) r.tail hdur
      (some (encodeFrom P P.genesis r.entries).length) (by simp) (fun n h => (Option.some.inj h).symm) true
    rw [hfull]
    refine ⟨?_, rfl, ?_, fun _ => by simp, fun h => h.elim⟩
    · simp [headFrom_append]
    · simp [Fs.contents]

/-- **A recovery cut by a crash**, computed: when the journal's directory entry is durable, what is left is the verified entries followed
by the first `j` entries of the settlement (the whole lines that reached the disk), and the directory entry is still durable. -/
theorem recover_cut_spec (hI : Inv P w) (hm : w.m.mode = .opened) (hs : w.fs.dirSafe = true) (cc : Cut) :
    ∃ r j, read P w.fs.contents = some r ∧ j ≤ (settleEntries r.entries).length ∧
      entriesOf P (w.step P (.recover w.m.gen (some cc))).fs.contents = r.entries ++ (settleEntries r.entries).take j ∧
      (w.step P (.recover w.m.gen (some cc))).fs.dirSafe = true := by
  rw [step_recover_opened w hm]
  by_cases hE : w.fs.contents = []
  · have hread0 : read P w.fs.contents = some ⟨[], P.genesis, []⟩ := by rw [hE]; exact read_empty
    refine ⟨⟨[], P.genesis, []⟩, 0, hread0, by simp [settleEntries, openCalls], ?_⟩
    simp only [recoverPlan, hE, read_empty, ite_true, Mode.isBusy]
    rw [finish_some]
    simp only [Fs.runPrefix, List.take_nil, List.foldl_nil]
    have hc := (crash_fs w.fs hI.pending ⟨_, hread0⟩ cc.keep cc.vanish).2.2 hs
    rw [hc]
    refine ⟨?_, hs⟩
    simp [entriesOf, hE, read_empty, settleEntries, openCalls]
  · obtain ⟨r, hrd⟩ := hI.readable
    obtain ⟨hd, hnl, hh⟩ := read_inv L _ r hrd
    have hdur : w.fs.durable = encodeFrom P P.genesis r.entries ++ r.tail := by
      rw [← contents_of_pending_nil hI.pending]; exact hd
    have hgood : w.fs.contents.length - r.tail.length = (encodeFrom P P.genesis r.entries).length := by
      rw [hd]; simp
    refine ⟨r, ?_⟩
    simp only [recoverPlan, hrd, hE, ite_false, ite_true, Mode.isBusy, hh, hgood]
    rw [finish_some]
    obtain ⟨h1, h2, h3⟩ := cut_read (P := P) L w.fs hI.pending r.entries (settleEntries r.entries) r.tail hnl hdur
      (some (encodeFrom P P.genesis r.entries).length) (by simp) (fun n h => (Option.some.inj h).symm)
      true cc.n cc.keep cc.vanish
    rcases h3 with ⟨j, r', hj, hr', he⟩ | ⟨_, h4⟩
    · refine ⟨j, trivial, hj, ?_, h2 hs⟩
      simp [entriesOf, hr', he]
    · simp [hs] at h4

end Lawful

end VbmJournal
