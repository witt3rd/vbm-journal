import VbmJournalProofs.Chain
/-! # Settling calls in flight (theorem (e), the list part)

`openCalls es` are the calls made and not completed; `settleEntries es` completes each as interrupted. Here: the open calls have no
duplicates; settling closes every one (`settle_closes`); settling again adds nothing (`settle_idem`); and settling a journal that a
crash cut in the middle of the settlement settles exactly the rest (`settle_partial`), so each call in flight is completed once
(`settle_once`) however recovery was interrupted. -/
namespace VbmJournal

theorem openStep_nodup (o : List Nat) (h : o.Nodup) (e : Entry) : (openStep o e).Nodup := by
  cases e with
  | note n => simpa [openStep] using h
  | body b => simpa [openStep] using h
  | call id =>
    by_cases hm : id ∈ o
    · simpa [openStep, hm] using h
    · simp only [openStep, hm, ite_false]
      rw [List.nodup_append]
      exact ⟨h, by simp, fun a ha b hb => by
        simp only [List.mem_singleton] at hb; subst hb; exact fun e => hm (e ▸ ha)⟩
  | done id b =>
    simp only [openStep]
    exact List.Pairwise.filter _ h

theorem foldl_openStep_nodup (es : List Entry) : ∀ o : List Nat, o.Nodup → (es.foldl openStep o).Nodup := by
  induction es with
  | nil => intro o h; exact h
  | cons e es ih => intro o h; exact ih _ (openStep_nodup o h e)

/-- The calls in flight are listed once each. -/
theorem openCalls_nodup (es : List Entry) : (openCalls es).Nodup :=
  foldl_openStep_nodup es [] List.nodup_nil

theorem openCalls_append (xs ys : List Entry) : openCalls (xs ++ ys) = ys.foldl openStep (openCalls xs) := by
  simp [openCalls, List.foldl_append]

theorem foldl_done (ids : List Nat) : ∀ (o : List Nat),
    (ids.map fun id => Entry.done id true).foldl openStep o = o.filter fun i => !(decide (i ∈ ids)) := by
  induction ids with
  | nil => intro o; exact (List.filter_eq_self.2 (by simp)).symm
  | cons a ids ih =>
    intro o
    simp only [List.map_cons, List.foldl_cons, openStep, ih, List.filter_filter]
    congr 1
    funext i
    by_cases h : i = a <;> simp [h]

/-- **Settling a journal cut in the middle of its settlement settles exactly the rest.** -/
theorem settle_partial (es : List Entry) (j : Nat) :
    settleEntries (es ++ (settleEntries es).take j) = (settleEntries es).drop j := by
  have hnd := openCalls_nodup es
  unfold settleEntries
  rw [← List.map_take, ← List.map_drop]
  rw [openCalls_append, foldl_done]
  congr 1
  generalize openCalls es = o at hnd
  have hsplit : o.filter (fun i => !(decide (i ∈ o.take j))) =
      (o.take j).filter (fun i => !(decide (i ∈ o.take j))) ++ (o.drop j).filter (fun i => !(decide (i ∈ o.take j))) := by
    rw [← List.filter_append, List.take_append_drop]
  rw [hsplit]
  have h1 : (o.take j).filter (fun i => !(decide (i ∈ o.take j))) = [] := by
    simp [List.filter_eq_nil_iff]
  have h2 : (o.drop j).filter (fun i => !(decide (i ∈ o.take j))) = o.drop j := by
    rw [List.filter_eq_self]
    intro a ha
    have hnd2 : (o.take j ++ o.drop j).Nodup := by rw [List.take_append_drop]; exact hnd
    have hd := (List.nodup_append.1 hnd2).2.2
    have hn : a ∉ o.take j := fun h => hd a h a ha rfl
    simpa using hn
  rw [h1, h2]; rfl

/-- **Every call in flight is settled**: after settling, none is open; settling again adds nothing. -/
theorem settle_idem (es : List Entry) : settleEntries (es ++ settleEntries es) = [] := by
  have := settle_partial es (settleEntries es).length
  simpa using this

theorem settle_closes (es : List Entry) : openCalls (es ++ settleEntries es) = [] := by
  have := settle_idem es
  simpa [settleEntries] using this

/-- The completions of call `id` in a journal. -/
def doneCount (id : Nat) (es : List Entry) : Nat :=
  es.countP fun e => match e with
    | .done i _ => i == id
    | _ => false

/-- **Settled exactly once**: a call in flight gains exactly one completion; a call not in flight gains none. -/
theorem settle_once (es : List Entry) (id : Nat) :
    doneCount id (es ++ settleEntries es) = doneCount id es + (if id ∈ openCalls es then 1 else 0) := by
  unfold doneCount settleEntries
  rw [List.countP_append, List.countP_map]
  have hc : (fun e => match e with | Entry.done i _ => i == id | _ => false) ∘ (fun id => Entry.done id true) = fun x => x == id := by
    funext x; rfl
  rw [hc, ← List.count_eq_countP, (openCalls_nodup es).count]

end VbmJournal
