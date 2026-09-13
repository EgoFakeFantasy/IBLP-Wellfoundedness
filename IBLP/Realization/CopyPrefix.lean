import IBLP.TracePieces
import IBLP.Realization.CopyPredecessor
import IBLP.RetainedTrace

namespace IBLP.FiniteBoundedData
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (D : FiniteBoundedData stage a)

include D in
theorem rawCopy_factorPrefix (nonempty : 0 < a.length) {b : IBLP.Pattern} {last : IBLP.Row}
    {minimum p target imageTarget start : Nat} {front : List Nat}
    (copy : IBLP.rawCopy a = some b) (hlast : a.getLast? = some last)
    (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (h : FactorPrefix a target start front) (tail : ∀ r ∈ front, p ≤ r)
    (targetImage : IBLP.copyEntry a.length last target = some imageTarget) :
    ∃ imageStart, IBLP.copyEntry a.length last start = some imageStart ∧
      FactorPrefix b imageTarget imageStart (front.map (· + (a.length - p))) := by
  induction h with
  | nil => exact ⟨imageTarget, targetImage, .nil⟩
  | @cons r next rows pred smaller inner ih =>
    obtain ⟨imageNext, nextImage, newInner⟩ := ih (fun s hs => tail s (List.mem_cons_of_mem r hs))
    have inTail := tail r (by simp)
    obtain ⟨otherNext, otherImage, newPred⟩ := D.rawCopy_predecessor_image nonempty copy hlast hm hp inTail pred
    have same : otherNext = imageNext := Option.some.inj (otherImage.symm.trans nextImage)
    subst otherNext
    have startImage := IBLP.copyEntry_tail (D.valid _ _ (IBLP.getLast_rowAt hlast)) hm hp inTail
    have bound : r ≤ a.length + 1 := (predecessor_row_index pred).2.trans (Nat.le_succ _)
    have less := D.copyEntry_strict nonempty (IBLP.getLast_rowAt hlast) hm hp bound smaller nextImage startImage
    exact ⟨r + (a.length - p), startImage, .cons newPred less newInner⟩

include D in
/-- The literal low-crossing chain: the translated initial factors are
followed directly by the original suffix beginning below the minimum. -/
theorem rawCopy_lowTrace (nonempty : 0 < a.length) {b : IBLP.Pattern} {last : IBLP.Row}
    {minimum p target start boundary : Nat} {front suffix : List Nat}
    (copy : IBLP.rawCopy a = some b) (hlast : a.getLast? = some last)
    (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (before : FactorPrefix a boundary start front) (after : FactorTrace a target boundary suffix)
    (tail : ∀ r ∈ front, p ≤ r) (low : boundary < minimum) (old : boundary < a.length) :
    ∃ imageStart, IBLP.copyEntry a.length last start = some imageStart ∧
      FactorTrace b target imageStart (front.map (· + (a.length - p)) ++ suffix) := by
  have boundaryImage : IBLP.copyEntry a.length last boundary = some boundary := by
    simp [IBLP.copyEntry, hm, hp, low]
  obtain ⟨imageStart, startImage, newBefore⟩ :=
    D.rawCopy_factorPrefix nonempty copy hlast hm hp before tail boundaryImage
  exact ⟨imageStart, startImage, newBefore.appendTrace (IBLP.rawCopy_factorTrace_old copy after old)⟩

include D in
/-- The high-crossing chain inserts precisely the control mark's old
accurate trace between the translated initial factors and the old suffix. -/
theorem rawCopy_highTrace (nonempty : 0 < a.length) {b : IBLP.Pattern} {last : IBLP.Row}
    {minimum p target start boundary imageBoundary : Nat} {front bridge suffix : List Nat}
    (copy : IBLP.rawCopy a = some b) (hlast : a.getLast? = some last)
    (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (before : FactorPrefix a boundary start front) (after : FactorTrace a target boundary suffix)
    (tail : ∀ r ∈ front, p ≤ r)
    (boundaryImage : IBLP.copyEntry a.length last boundary = some imageBoundary)
    (control : FactorTrace a boundary imageBoundary bridge) (old : imageBoundary < a.length) :
    ∃ imageStart, IBLP.copyEntry a.length last start = some imageStart ∧
      FactorTrace b target imageStart (front.map (· + (a.length - p)) ++ (bridge ++ suffix)) := by
  obtain ⟨imageStart, startImage, newBefore⟩ :=
    D.rawCopy_factorPrefix nonempty copy hlast hm hp before tail boundaryImage
  exact ⟨imageStart, startImage,
    newBefore.appendTrace (IBLP.rawCopy_factorTrace_old copy (control.append after) old)⟩

end IBLP.FiniteBoundedData
