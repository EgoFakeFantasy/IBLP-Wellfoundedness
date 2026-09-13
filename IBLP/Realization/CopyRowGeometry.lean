import IBLP.Realization.CopyEntryImage
import IBLP.Columns

namespace IBLP.FiniteBoundedData
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (D : FiniteBoundedData stage a)

include D in
theorem copy_columns_sorted (nonempty : 0 < a.length) {last : IBLP.Row} {minimum p : Nat}
    (hr : rowAt a a.length = some last) (hm : last.columns.head? = some minimum)
    (hp : last.p = some p) {xs ys : List Nat} (sorted : xs.Pairwise (· < ·))
    (bound : ∀ x ∈ xs, x ≤ a.length + 1)
    (copied : xs.mapM (IBLP.copyEntry a.length last) = some ys) : ys.Pairwise (· < ·) := by
  have mapped := option_mapM_forall2 copied
  clear copied
  induction mapped with
  | nil => exact List.Pairwise.nil
  | @cons x y xs ys hx ht ih =>
    obtain ⟨first, rest⟩ := List.pairwise_cons.mp sorted
    apply List.pairwise_cons.mpr
    refine ⟨?_, ih rest (fun w hw => bound w (List.mem_cons_of_mem x hw))⟩
    intro z hz
    obtain ⟨w, hw, image⟩ := ht.mem_right hz
    exact D.copyEntry_strict nonempty hr hm hp (bound w (List.mem_cons_of_mem x hw))
      (first w hw) hx image

/-- This is a description of the actual successful program output. It
retains exactly the program's three-branch mark filter. -/
theorem copyRow_description {last row copied : IBLP.Row} {r : Nat}
    (hr : rowAt a r = some row) (hc : IBLP.copyRow a last r = some copied) :
    ∃ cols marks,
      row.columns.mapM (IBLP.copyEntry a.length last) = some cols ∧
      (row.marks.filter (fun y => y ∈ row.columns &&
        keepCopiedMark a last r row (IBLP.canonicalColumns cols) y)).mapM
          (IBLP.copyEntry a.length last) = some marks ∧
      copied = ⟨IBLP.canonicalColumns cols, row.step, IBLP.canonicalColumns marks⟩ := by
  unfold IBLP.copyRow at hc
  obtain ⟨selected, hselected, hc⟩ := Option.bind_eq_some_iff.mp hc
  have same : selected = row := Option.some.inj (hselected.symm.trans hr)
  subst selected
  obtain ⟨cols, hcols, hc⟩ := Option.bind_eq_some_iff.mp hc
  obtain ⟨marks, hmarks, hc⟩ := Option.bind_eq_some_iff.mp hc
  exact ⟨cols, marks, hcols, hmarks, (Option.some.inj hc).symm⟩

include D in
theorem copyRow_columns (nonempty : 0 < a.length) {last row copied : IBLP.Row}
    {minimum p r : Nat} (hlast : rowAt a a.length = some last)
    (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (hr : rowAt a r = some row) (hc : IBLP.copyRow a last r = some copied) :
    FullMarkedBLP.MapsEntries (IBLP.copyEntry a.length last) row.columns copied.columns ∧
      copied.columns.Pairwise (· < ·) ∧ copied.step = row.step := by
  obtain ⟨cols, marks, mapped, _, rfl⟩ := copyRow_description hr hc
  have bound (x : Nat) (hx : x ∈ row.columns) : x ≤ a.length + 1 :=
    (Row.column_le_last (D.valid _ _ hr) hx).trans ((rowAt_le_length hr).trans (Nat.le_succ _))
  have sorted := D.copy_columns_sorted nonempty hlast hm hp (D.valid _ _ hr).1 bound mapped
  simp only [IBLP.canonicalColumns_of_sorted sorted]
  exact ⟨option_mapM_forall2 mapped, sorted, trivial⟩

include D in
theorem copyRow_shape (nonempty : 0 < a.length) {last row copied : IBLP.Row}
    {minimum p r : Nat} (hlast : rowAt a a.length = some last)
    (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (hr : rowAt a r = some row) (hc : IBLP.copyRow a last r = some copied) : copied.OrdinaryShape := by
  obtain ⟨mapped, _, step⟩ := D.copyRow_columns nonempty hlast hm hp hr hc
  have shape := D.shapes row (rowAt_mem hr)
  simpa only [IBLP.Row.OrdinaryShape, mapped.length_eq, step] using shape

theorem copyRow_mark_origin {last row copied : IBLP.Row} {r b : Nat}
    (hr : rowAt a r = some row) (hc : IBLP.copyRow a last r = some copied)
    (member : b ∈ copied.marks) :
    ∃ source, source ∈ row.marks ∧ source ∈ row.columns ∧
      keepCopiedMark a last r row copied.columns source = true ∧
      IBLP.copyEntry a.length last source = some b := by
  obtain ⟨cols, marks, _, mapped, rfl⟩ := copyRow_description hr hc
  have hm := (IBLP.mem_canonicalColumns b marks).mp member
  obtain ⟨source, hs, edge⟩ := (option_mapM_forall2 mapped).mem_right hm
  have filtered := List.mem_filter.mp hs
  have condition : source ∈ row.columns ∧
      keepCopiedMark a last r row (IBLP.canonicalColumns cols) source = true := by
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using filtered.2
  exact ⟨source, filtered.1, condition.1, condition.2, edge⟩

include D in
theorem copyRow_valid (nonempty : 0 < a.length) {last row copied : IBLP.Row}
    {minimum p r : Nat} (hlast : rowAt a a.length = some last)
    (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (hr : rowAt a r = some row) (tail : p ≤ r)
    (hc : IBLP.copyRow a last r = some copied) : copied.BasicValid (r + (a.length - p)) := by
  obtain ⟨mapped, sorted, _⟩ := D.copyRow_columns nonempty hlast hm hp hr hc
  have valid := D.valid _ _ hr
  refine ⟨sorted, ?_, ?_, ?_⟩
  · rw [← mapped.length_eq]
    exact valid.2.1
  · obtain ⟨owner, lastValue, image⟩ := mapped.last valid.2.2.1
    have expected := IBLP.copyEntry_tail (D.valid _ _ hlast) hm hp tail
    have same := Option.some.inj (image.symm.trans expected)
    exact lastValue.trans (congrArg some same)
  · intro b hb
    obtain ⟨source, _, sourceColumn, _, image⟩ := copyRow_mark_origin hr hc hb
    obtain ⟨value, member, hvalue⟩ := IBLP.mapped_mem_left mapped sourceColumn
    have same := Option.some.inj (hvalue.symm.trans image)
    exact same ▸ member

include D in
theorem copyRow_proper (nonempty : 0 < a.length) {last row copied : IBLP.Row}
    {minimum p r : Nat} (hlast : rowAt a a.length = some last)
    (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (hr : rowAt a r = some row) (proper : ∀ b ∈ row.marks, row.ProperMark b)
    (hc : IBLP.copyRow a last r = some copied) : ∀ b ∈ copied.marks, copied.ProperMark b := by
  obtain ⟨mapped, _, step⟩ := D.copyRow_columns nonempty hlast hm hp hr hc
  intro b hb
  obtain ⟨source, marked, _, _, image⟩ := copyRow_mark_origin hr hc hb
  obtain ⟨i, hi, above, below⟩ := proper source marked
  obtain ⟨value, atIndex, atImage⟩ := mapped.at_left hi
  have same := Option.some.inj (atImage.symm.trans image)
  refine ⟨i, atIndex.trans (congrArg some same), ?_, ?_⟩
  · simpa only [step] using above
  · simpa only [← mapped.length_eq] using below

end IBLP.FiniteBoundedData
