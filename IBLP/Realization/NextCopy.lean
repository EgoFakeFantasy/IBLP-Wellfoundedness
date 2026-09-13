import IBLP.Realization.RawCopyData
import IBLP.RawCopyLast
import IBLP.CopyEntryIterate
import IBLP.CopyRowTotal

namespace IBLP.FiniteBoundedData
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (D : FiniteBoundedData stage a)

include D in
theorem copied_control (nonempty : 0 < a.length) {last next : IBLP.Row} {minimum p : Nat}
    (hlast : rowAt a a.length = some last) (hm : last.columns.head? = some minimum)
    (hp : last.p = some p) (copied : IBLP.copyRow a last a.length = some next) :
    next.p = some a.length ∧ ∃ minimum', next.columns.head? = some minimum' ∧ minimum ≤ minimum' := by
  obtain ⟨mapped, _, step⟩ := D.copyRow_columns nonempty hlast hm hp hlast copied
  have pred : IBLP.predecessor a a.length = some p := by simp [IBLP.predecessor, hlast, hp]
  have pn := IBLP.predecessor_lt D.valid D.shapes pred
  obtain ⟨newP, atP, pImage⟩ := IBLP.mapped_fromRight_left mapped hp
  have expected : IBLP.copyEntry a.length last p = some a.length := by
    have image := IBLP.copyEntry_tail (D.valid _ _ hlast) hm hp (show p ≤ p from le_rfl)
    simpa only [Nat.add_sub_of_le pn.le] using image
  have same : newP = a.length := Option.some.inj (pImage.symm.trans expected)
  have nextPred : next.p = some a.length := by
    simpa only [IBLP.Row.p, step, same] using atP
  obtain ⟨minimum', atMinimum, image⟩ := mapped.at_left
    (show last.columns[0]? = some minimum by simpa only [List.head?_eq_getElem?] using hm)
  exact ⟨nextPred, minimum', by simpa only [List.head?_eq_getElem?] using atMinimum,
    IBLP.copyEntry_inflationary (D.valid _ _ hlast) (D.shapes last (rowAt_mem hlast)) hm hp image⟩

include D in
/-- Actual success of the first full-tail copy implies actual success of
the next copy; no tree well-foundedness or next-step totality is assumed. -/
theorem rawCopy_next_exists {b : IBLP.Pattern} (copy : IBLP.rawCopy a = some b) :
    ∃ c, IBLP.rawCopy b = some c := by
  obtain ⟨last, p, _, hlast, hp, positive, included, _, _⟩ := IBLP.rawCopy_decomposition copy
  have nonempty : 0 < a.length := positive.trans_le included
  have atLast := IBLP.getLast_rowAt hlast
  have length := IBLP.rawCopy_length copy hlast hp
  have headBound : 0 < last.columns.length := by have := (D.valid _ _ atLast).2.1; omega
  let minimum := last.columns[0]'headBound
  have hm : last.columns.head? = some minimum := by
    simp only [List.head?_eq_getElem?, List.getElem?_eq_getElem headBound, minimum]
  obtain ⟨next, hnext, copiedNext⟩ := IBLP.rawCopy_last copy hlast hp
  obtain ⟨hpNext, minimum', hmNext, minimumLe⟩ := D.copied_control nonempty atLast hm hp copiedNext
  obtain ⟨controlMap, _, step⟩ := D.copyRow_columns nonempty atLast hm hp atLast copiedNext
  apply IBLP.rawCopy_exists_of_entries hnext hpNext nonempty (by omega)
  intro r row lower upper atRow x hx
  obtain ⟨source, _, _, _, copiedRow⟩ := IBLP.rawCopy_row_origin copy hlast hp lower atRow
  obtain ⟨oldRow, atSource, _⟩ := Option.bind_eq_some_iff.mp copiedRow
  have mapped := (D.copyRow_columns nonempty atLast hm hp atSource copiedRow).1
  obtain ⟨oldX, _, image⟩ := mapped.mem_right hx
  exact IBLP.copyEntry_next_exists hm hp included hmNext hpNext minimumLe step controlMap image

include D in
theorem rawCopies_exists (proper : IBLP.ProperMarks a) (first : ∃ b, IBLP.rawCopy a = some b)
    (m : Nat) : ∃ b, IBLP.rawCopies m a = some b := by
  induction m generalizing stage a with
  | zero => exact ⟨a, rfl⟩
  | succ m ih =>
    obtain ⟨b, copy⟩ := first
    obtain ⟨last, p, _, hlast, hp, positive, included, _, _⟩ := IBLP.rawCopy_decomposition copy
    have nonempty : 0 < a.length := positive.trans_le included
    have atLast := IBLP.getLast_rowAt hlast
    have headBound : 0 < last.columns.length := by have := (D.valid _ _ atLast).2.1; omega
    let minimum := last.columns[0]'headBound
    have hm : last.columns.head? = some minimum := by
      simp only [List.head?_eq_getElem?, List.getElem?_eq_getElem headBound, minimum]
    let nextData := D.rawCopyData nonempty proper copy hlast hm hp
    have nextProper := (D.rawCopy_geometry proper copy).2.2
    obtain ⟨c, hc⟩ := ih nextData nextProper (D.rawCopy_next_exists copy)
    exact ⟨c, by simp [IBLP.rawCopies, copy, hc]⟩

end IBLP.FiniteBoundedData
