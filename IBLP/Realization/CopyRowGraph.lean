import IBLP.Realization.CopyRowGeometry
import IBLP.MappedColumns
import IBLP.Model.InternalGraphImage
import IBLP.Model.WeakAgreementImage

namespace IBLP.FiniteBoundedData
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (D : FiniteBoundedData stage a)

def rowIndex {r : Nat} {row : IBLP.Row} (hr : rowAt a r = some row) : FiniteRowIndex a :=
  ⟨r, rowAt_pos hr, rowAt_le_length hr⟩

include D in
theorem copyRow_full_columns (nonempty : 0 < a.length) {last row copied : IBLP.Row}
    {minimum p r : Nat} (hlast : rowAt a a.length = some last)
    (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (hr : rowAt a r = some row) (tail : p ≤ r) (hc : IBLP.copyRow a last r = some copied) :
    MapsEntries (IBLP.copyEntry a.length last) (row.columns ++ [r + 1])
      (copied.columns ++ [r + (a.length - p) + 1]) := by
  have cols := (D.copyRow_columns nonempty hlast hm hp hr hc).1
  apply mapped_append cols
  apply MapsEntries.cons _ MapsEntries.nil
  have image := IBLP.copyEntry_tail (D.valid _ _ hlast) hm hp (show p ≤ r + 1 by omega)
  simpa only [Nat.add_right_comm r 1 (a.length - p)] using image

theorem copyRow_graph_critical (nonempty : 0 < a.length) {last row copied : IBLP.Row}
    {minimum p r c : Nat} (hlast : rowAt a a.length = some last)
    (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (hr : rowAt a r = some row) (hc : IBLP.copyRow a last r = some copied)
    (head : copied.columns.head? = some c) :
    (D.lastExtension nonempty).next.model.GraphCriticalPoint
      ((D.lastExtension nonempty).embedding (D.graph (rowIndex hr)))
      ((D.lastExtension nonempty).next.ordinal (D.copyPoint nonempty p c)) := by
  obtain ⟨mapped, _, _⟩ := D.copyRow_columns nonempty hlast hm hp hr hc
  obtain ⟨old, atOld, image⟩ := mapped.at
    (show copied.columns[0]? = some c by simpa only [List.head?_eq_getElem?] using head)
  have oldHead : row.columns.head? = some old := by simpa only [List.head?_eq_getElem?] using atOld
  rw [D.copyEntry_image nonempty hlast hm hp image]
  exact (stage.graphCriticalPoint_image (D.lastExtension nonempty).next
    (D.lastExtension nonempty).embedding _ _).mpr (D.critical (rowIndex hr) row old hr oldHead)

theorem copyRow_graph_elementary (nonempty : 0 < a.length) {last row copied : IBLP.Row}
    {minimum p r e : Nat} (hlast : rowAt a a.length = some last)
    (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (hr : rowAt a r = some row) (tail : p ≤ r) (hc : IBLP.copyRow a last r = some copied)
    (endpoint : copied.e = some e) :
    (D.lastExtension nonempty).next.InternalGraphElementary
      (D.copyPoint nonempty p e) (D.copyPoint nonempty p (r + (a.length - p) + 1))
      ((D.lastExtension nonempty).embedding (D.graph (rowIndex hr))) := by
  obtain ⟨mapped, _, step⟩ := D.copyRow_columns nonempty hlast hm hp hr hc
  have hfrom : IBLP.fromRight copied.columns row.step = some e := by
    simpa only [IBLP.Row.e, step] using endpoint
  obtain ⟨old, oldEnd, image⟩ := mapped_fromRight mapped hfrom
  have oldEndpoint : row.e = some old := oldEnd
  have pred : IBLP.predecessor a a.length = some p := by simp [IBLP.predecessor, hlast, hp]
  have index : r + (a.length - p) + 1 = (r + 1) + (a.length - p) := by omega
  rw [D.copyEntry_image nonempty hlast hm hp image, index,
    D.copyPoint_tail nonempty pred (r + 1) (by omega)]
  apply (stage.internalGraphElementary_image (D.lastExtension nonempty).next
    (D.lastExtension nonempty).embedding _ _ _).mpr
  have source := D.source_eq hr oldEndpoint
  simpa only [← source] using D.elementary (rowIndex hr)

theorem copyRow_graph_edges (nonempty : 0 < a.length) {last row copied : IBLP.Row}
    {minimum p r : Nat} (hlast : rowAt a a.length = some last)
    (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (hr : rowAt a r = some row) (tail : p ≤ r) (hc : IBLP.copyRow a last r = some copied) :
    ∀ edge ∈ copied.edgePairs (r + (a.length - p)),
      ZFSet.pair (D.copyPoint nonempty p edge.1).toZFSet (D.copyPoint nonempty p edge.2).toZFSet ∈
        ((D.lastExtension nonempty).embedding (D.graph (rowIndex hr))).val := by
  have full := D.copyRow_full_columns nonempty hlast hm hp hr tail hc
  have step := (D.copyRow_columns nonempty hlast hm hp hr hc).2.2
  intro edge member
  have member' : edge ∈ (copied.columns ++ [r + (a.length - p) + 1]).zip
      ((copied.columns ++ [r + (a.length - p) + 1]).drop row.step) := by
    simpa only [IBLP.Row.edgePairs, step] using member
  obtain ⟨old, oldEdge, first, second⟩ := mapped_zip_drop full row.step member'
  have oldValue := D.edges (rowIndex hr) row hr old oldEdge
  have interpreted := (stage.model.graphApplies_absolute (D.graph (rowIndex hr))
    (stage.ordinal (D.point old.1)) (stage.ordinal (D.point old.2))).mpr oldValue
  have transported := ((D.lastExtension nonempty).embedding.graphApplies_iff _ _ _).mpr interpreted
  have actual := ((D.lastExtension nonempty).next.model.graphApplies_absolute _ _ _).mp transported
  rw [D.copyEntry_image nonempty hlast hm hp first, D.copyEntry_image nonempty hlast hm hp second]
  simpa only [stage.ordinalImage_compat] using actual

end IBLP.FiniteBoundedData
