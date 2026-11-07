import VbmJournalProofs.Chain
/-! # What a plan does to a file, and what a crash leaves

Facts about `Fs.run`, `Fs.crash` and `commitPlan`, used by the world theorems. -/
namespace VbmJournal

/-- The file's bytes after the optional truncate of a plan. -/
def cutBase (cut : Option Nat) (dur : Bytes) : Bytes :=
  match cut with
  | some n => dur.take n
  | none => dur

theorem contents_of_pending_nil {f : Fs} (h : f.pending = []) : f.contents = f.durable := by
  simp [Fs.contents, h]

/-- A plan that completes leaves the base, then everything written, durable; the directory entry durable if asked. -/
theorem commit_all (f : Fs) (hp : f.pending = []) (cut : Option Nat) (S : Bytes) (dir : Bool) :
    f.runAll (commitPlan cut S dir) = ⟨cutBase cut f.durable ++ S, [], f.dirSafe || dir⟩ := by
  obtain ⟨d, p, s⟩ := f
  simp only at hp
  subst hp
  cases cut <;> by_cases hS : S = [] <;> cases dir <;>
    simp [commitPlan, Fs.runAll, Fs.run, cutBase, hS]

/-- A directory entry that is durable stays durable under every effect. -/
theorem run_dirSafe (f : Fs) (h : f.dirSafe = true) (e : Effect) : (f.run e).dirSafe = true := by
  cases e <;> simp [Fs.run, h]

theorem foldl_dirSafe (plan : List Effect) : ∀ (f : Fs), f.dirSafe = true → (plan.foldl Fs.run f).dirSafe = true := by
  induction plan with
  | nil => intro f h; exact h
  | cons e es ih => intro f h; exact ih _ (run_dirSafe f h e)

/-- A crash at any point of a plan: the file keeps its base, or the base and a prefix of what was written (the whole of it if the plan
got that far), or, when its directory entry was never durable, it is gone. A durable directory entry stays. -/
theorem commit_cut (f : Fs) (hp : f.pending = []) (cut : Option Nat) (S : Bytes) (dir : Bool) (n keep : Nat) (vanish : Bool) :
    ((f.runPrefix n (commitPlan cut S dir)).crash keep vanish).pending = [] ∧
    (f.dirSafe = true → ((f.runPrefix n (commitPlan cut S dir)).crash keep vanish).dirSafe = true) ∧
    ∃ k, k ≤ S.length ∧
      (((f.runPrefix n (commitPlan cut S dir)).crash keep vanish).durable = f.durable ∨
       ((f.runPrefix n (commitPlan cut S dir)).crash keep vanish).durable = cutBase cut f.durable ++ S.take k ∨
       (((f.runPrefix n (commitPlan cut S dir)).crash keep vanish).durable = [] ∧ f.dirSafe = false)) := by
  obtain ⟨d, p, s⟩ := f
  simp only at hp
  subst hp
  cases cut <;> by_cases hS : S = [] <;> cases dir <;> rcases n with _ | _ | _ | _ | n <;> cases s <;> cases vanish <;>
    simp [commitPlan, Fs.runPrefix, Fs.run, Fs.crash, Fs.empty, cutBase, hS]
  all_goals first
    | exact ⟨0, Nat.zero_le _⟩
    | (refine ⟨0, Nat.zero_le _, ?_⟩; simp; done)
    | (refine ⟨S.length, Nat.le_refl _, ?_⟩; simp; done)
    | (refine ⟨min keep S.length, Nat.min_le_right _ _, ?_⟩; simp; done)

end VbmJournal
