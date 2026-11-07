/-! # vbm-journal slice 3, part 1: a flat buffer is its list

The proofs keep their list shape (`VbmJournal.Bytes` is `List UInt8`); the compiled code reads and hashes `ByteArray`s, which are flat. A `ByteArray`
is its list (`ByteArray.toList`) and a list is a `ByteArray` (`List.toByteArray`): these are the facts the refinement theorems (`VbmJournalProofs.Flat`)
and the flat-buffer fields of `Params` rest on. `Init` only. -/
namespace VbmJournal

theorem toList_loop (b : ByteArray) : ∀ (i : Nat) (r : List UInt8),
    ByteArray.toList.loop b i r = r.reverse ++ b.data.toList.drop i := by
  intro i r
  fun_induction ByteArray.toList.loop b i r with
  | case1 i r h ih =>
    rw [ih]
    have hi : i < b.data.toList.length := by simpa using h
    have : b.get! i = b.data.toList[i] := by
      simp [ByteArray.get!, h]
    rw [this, List.drop_eq_getElem_cons hi]
    simp
  | case2 i r h =>
    have : b.data.toList.drop i = [] := List.drop_eq_nil_of_le (by simp at h ⊢; omega)
    simp [this]

/-- `ByteArray.toList` is the list of the underlying array. -/
theorem toList_eq (b : ByteArray) : b.toList = b.data.toList := by
  simp [ByteArray.toList, toList_loop]

/-- A list, made flat and read back, is itself. -/
@[simp] theorem toList_toByteArray (l : List UInt8) : l.toByteArray.toList = l := by
  simp [toList_eq]

/-- A flat buffer, made a list and flat again, is itself. -/
@[simp] theorem toByteArray_toList (b : ByteArray) : b.toList.toByteArray = b := by
  apply ByteArray.ext
  apply Array.ext'
  simp [toList_eq]

@[simp] theorem length_toList (b : ByteArray) : b.toList.length = b.size := by
  simp [toList_eq]

theorem toList_extract (b : ByteArray) (i j : Nat) : (b.extract i j).toList = (b.toList.drop i).take (j - i) := by
  simp [toList_eq]

theorem toList_append (a b : ByteArray) : (a ++ b).toList = a.toList ++ b.toList := by
  simp [toList_eq]

theorem toByteArray_append (a b : List UInt8) : (a ++ b).toByteArray = a.toByteArray ++ b.toByteArray := by
  simp

end VbmJournal
