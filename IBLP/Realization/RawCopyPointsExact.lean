import IBLP.Realization.RawCopyData

namespace IBLP.FiniteBoundedData
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (D : FiniteBoundedData stage a)

theorem rawCopyData_point_old (nonempty : 0 < a.length) {b : IBLP.Pattern} {last : IBLP.Row}
    {minimum p : Nat} (proper : IBLP.ProperMarks a) (copy : IBLP.rawCopy a = some b)
    (hlast : a.getLast? = some last) (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (i : Nat) (old : i ≤ a.length) : (D.rawCopyData nonempty proper copy hlast hm hp).point i = D.point i := by
  have length := IBLP.rawCopy_length copy hlast hp
  change finiteThetaExtension (D.rawCopyTheta nonempty p b) i = D.point i
  rw [D.rawCopyTheta_at nonempty p b i (by omega), D.copyPoint_old nonempty p i old]

theorem rawCopyData_point_image (nonempty : 0 < a.length) {b : IBLP.Pattern} {last : IBLP.Row}
    {minimum p x y : Nat} (proper : IBLP.ProperMarks a) (copy : IBLP.rawCopy a = some b)
    (hlast : a.getLast? = some last) (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (inside : x ≤ a.length + 1) (image : IBLP.copyEntry a.length last x = some y) :
    (D.rawCopyData nonempty proper copy hlast hm hp).point y =
      stage.ordinalImage (D.lastExtension nonempty).embedding (D.point x) := by
  have length := IBLP.rawCopy_length copy hlast hp
  have bound := IBLP.copyEntry_bound (D.valid _ _ (IBLP.getLast_rowAt hlast)) hm hp inside image
  change finiteThetaExtension (D.rawCopyTheta nonempty p b) y = _
  rw [D.rawCopyTheta_at nonempty p b y (by omega)]
  exact D.copyEntry_image nonempty (IBLP.getLast_rowAt hlast) hm hp image

theorem rawCopyData_lastPoint (nonempty : 0 < a.length) {b : IBLP.Pattern} {last : IBLP.Row}
    {minimum p : Nat} (proper : IBLP.ProperMarks a) (copy : IBLP.rawCopy a = some b)
    (hlast : a.getLast? = some last) (hm : last.columns.head? = some minimum) (hp : last.p = some p) :
    (D.rawCopyData nonempty proper copy hlast hm hp).point b.length =
      stage.ordinalImage (D.lastExtension nonempty).embedding (D.point a.length) := by
  have pred : IBLP.predecessor a a.length = some p := by
    simp [IBLP.predecessor, IBLP.getLast_rowAt hlast, hp]
  change finiteThetaExtension (D.rawCopyTheta nonempty p b) b.length = _
  rw [D.rawCopyTheta_at nonempty p b b.length (by omega), IBLP.rawCopy_length copy hlast hp]
  exact D.copyPoint_tail nonempty pred a.length (IBLP.predecessor_lt D.valid D.shapes pred).le

end IBLP.FiniteBoundedData
