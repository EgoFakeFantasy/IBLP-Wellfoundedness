import IBLP.Realization.NativeImages
import IBLP.Realization.CopyPoints
import FullMarkedBLP.NativeColumnOrder

namespace IBLP.FiniteBoundedData
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (D : FiniteBoundedData stage a)

/-- Records are descending; new points use their ascending order. -/
noncomputable def nativeFresh (r : FiniteRowIndex a) (sources : List Nat) (j : Nat) : Ordinal.{u} :=
  D.nativeImage r (sources.reverse[j]?.getD 0)

theorem nativeFresh_at (r : FiniteRowIndex a) (sources : List Nat) (j : Nat) (bound : j < sources.length) :
    D.nativeFresh r sources j = D.nativeImage r (sources.reverse[j]'(by simpa using bound)) := by
  have read : sources.reverse[j]? = some (sources.reverse[j]'(by simpa using bound)) :=
    List.getElem?_eq_some_iff.mpr ⟨by simpa using bound, rfl⟩
  unfold nativeFresh
  rw [read]
  rfl

theorem nativeFresh_gap (r : FiniteRowIndex a) {row : IBLP.Row} {p e : Nat} {sources : List Nat}
    (hr : IBLP.rowAt a r.val = some row) (hp : row.p = some p) (he : row.e = some e)
    (run : IBLP.nativeSources a r.val = some sources) (j : Nat) (bound : j < sources.length) :
    D.point r.val < D.nativeFresh r sources j ∧ D.nativeFresh r sources j < D.point (r.val + 1) := by
  rw [D.nativeFresh_at r sources j bound]
  apply D.nativeSource_image_gap r hr hp he run
  exact List.mem_reverse.mp (List.getElem_mem (by simpa using bound))

theorem nativeFresh_strict (r : FiniteRowIndex a) {row : IBLP.Row} {p e : Nat} {sources : List Nat}
    (hr : IBLP.rowAt a r.val = some row) (hp : row.p = some p) (he : row.e = some e)
    (run : IBLP.nativeSources a r.val = some sources) (i j : Nat) (less : i < j) (bound : j < sources.length) :
    D.nativeFresh r sources i < D.nativeFresh r sources j := by
  have ib : i < sources.length := by omega
  have ib' : i < sources.reverse.length := by simpa using ib
  have jb' : j < sources.reverse.length := by simpa using bound
  rw [D.nativeFresh_at r sources i ib, D.nativeFresh_at r sources j bound]
  have sorted : sources.reverse.Pairwise (· < ·) := by
    simpa only [List.pairwise_reverse] using IBLP.nativeSources_decreasing D.valid run
  have si := IBLP.nativeSources_bounds D.valid hr hp he run _
    (List.mem_reverse.mp (List.getElem_mem (by simpa using ib : i < sources.reverse.length)))
  have sj := IBLP.nativeSources_bounds D.valid hr hp he run _
    (List.mem_reverse.mp (List.getElem_mem (by simpa using bound : j < sources.reverse.length)))
  have endpoint := rowEndpoint_eq hr he
  apply D.nativeImage_strictMonoOn r
  · change sources.reverse[i] ≤ rowEndpoint a r.val; omega
  · change sources.reverse[j] ≤ rowEndpoint a r.val; omega
  · exact List.pairwise_iff_getElem.mp sorted i j (by simpa using ib) (by simpa using bound) less

/-- The full finite point insertion for the original native operation. -/
noncomputable def nativePoint (r : FiniteRowIndex a) (sources : List Nat) (i : Nat) : Ordinal.{u} :=
  FullMarkedBLP.nativeColumnValues D.point (D.nativeFresh r sources) r.val sources.length i

theorem nativePoint_increasing (r : FiniteRowIndex a) {row : IBLP.Row} {p e : Nat} {sources : List Nat}
    (hr : IBLP.rowAt a r.val = some row) (hp : row.p = some p) (he : row.e = some e)
    (run : IBLP.nativeSources a r.val = some sources) :
    StrictMonoOn (D.nativePoint r sources) (Set.Iic (a.length + sources.length + 1)) := by
  intro i hi j hj less
  change j ≤ a.length + sources.length + 1 at hj
  apply FullMarkedBLP.nativeColumnValues_strict D.point (D.nativeFresh r sources) r.val sources.length (a.length + 1)
    (by have := r.property.2; omega)
    (fun i j less bound => D.point_increasing (by change i ≤ a.length + 1; omega) bound less)
    (D.nativeFresh_strict r hr hp he run)
    (fun k bound => (D.nativeFresh_gap r hr hp he run k bound).1)
    (fun k bound => (D.nativeFresh_gap r hr hp he run k bound).2) less
  omega

theorem nativePoint_inaccessible (r : FiniteRowIndex a) (sources : List Nat) (i : Nat) :
    stage.model.InternalInaccessible (stage.ordinal (D.nativePoint r sources i)) := by
  unfold nativePoint FullMarkedBLP.nativeColumnValues
  split
  · exact D.point_inaccessible _
  · split
    · exact D.nativeImage_inaccessible r _
    · exact D.point_inaccessible _

theorem nativePoint_old (r : FiniteRowIndex a) (sources : List Nat) (i : Nat) :
    D.nativePoint r sources (IBLP.shiftAfter r.val sources.length i) = D.point i :=
  FullMarkedBLP.nativeColumnValues_preserves D.point (D.nativeFresh r sources) r.val sources.length i

theorem nativePoint_inserted (r : FiniteRowIndex a) (sources : List Nat) (j : Nat) (bound : j < sources.length) :
    D.nativePoint r sources (r.val + 1 + j) = D.nativeFresh r sources j :=
  FullMarkedBLP.nativeColumnValues_inserted D.point (D.nativeFresh r sources) r.val sources.length j bound

theorem nativePoint_top (r : FiniteRowIndex a) (sources : List Nat) :
    D.nativePoint r sources (a.length + sources.length + 1) = D.top := by
  have exactTop := D.nativePoint_old r sources (a.length + 1)
  have shifted : IBLP.shiftAfter r.val sources.length (a.length + 1) = a.length + sources.length + 1 := by
    simp only [IBLP.shiftAfter, if_pos (by have := r.property.2; omega : r.val < a.length + 1)]
    omega
  rw [shifted, D.point_top] at exactTop
  exact exactTop

end IBLP.FiniteBoundedData
