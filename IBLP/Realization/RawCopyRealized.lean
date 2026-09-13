import IBLP.Realization.CopiedMarks

namespace IBLP.MarkedRealization
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (R : MarkedRealization stage a)

/-- Complete semantic closure of the original single raw copy: the actual
next model, all spliced points and whole row graphs, proper marks, exact
traces and every retained/copied weak certificate. Intermediate saturation
is not imposed; the manuscript restores it after the frozen scan. -/
noncomputable def rawCopy (nonempty : 0 < a.length) {b : IBLP.Pattern} {last : IBLP.Row}
    {minimum p : Nat} (copy : IBLP.rawCopy a = some b) (hlast : a.getLast? = some last)
    (hm : last.columns.head? = some minimum) (hp : last.p = some p) :
    MarkedRealization (R.data.lastExtension nonempty).next b where
  data := R.data.rawCopyData nonempty R.proper copy hlast hm hp
  proper := (R.data.rawCopy_geometry R.proper copy).2.2
  marks := by
    intro r row mark hr marked
    by_cases old : r < a.length
    · have oldRow := (IBLP.rawCopy_prefix copy old).symm.trans hr
      exact R.rawCopy_markRealized_old nonempty copy hlast hm hp oldRow old marked
    · obtain ⟨source, tail, _, owner, rowCopy⟩ := IBLP.rawCopy_row_origin copy hlast hp (by omega) hr
      obtain ⟨sourceRow, sourceAt, _⟩ := Option.bind_eq_some_iff.mp rowCopy
      have certificate := R.copied_markRealized nonempty copy hlast hm hp sourceAt tail rowCopy marked
      exact owner.symm ▸ certificate

theorem rawCopy_top (nonempty : 0 < a.length) {b : IBLP.Pattern} {last : IBLP.Row}
    {minimum p : Nat} (copy : IBLP.rawCopy a = some b) (hlast : a.getLast? = some last)
    (hm : last.columns.head? = some minimum) (hp : last.p = some p) :
    (R.rawCopy nonempty copy hlast hm hp).top =
      stage.ordinalImage (R.data.lastExtension nonempty).embedding R.top :=
  R.data.rawCopyData_top nonempty R.proper copy hlast hm hp

end IBLP.MarkedRealization
