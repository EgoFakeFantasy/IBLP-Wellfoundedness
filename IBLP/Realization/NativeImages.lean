import IBLP.Realization.BoundedRealization
import IBLP.Model.ReadOrdinalEdge
import IBLP.NativeWalk

namespace IBLP.FiniteBoundedData
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (D : FiniteBoundedData stage a)

/-- Native points are values of the actual saved bounded map. -/
noncomputable def nativeImage (r : FiniteRowIndex a) (s : Nat) : Ordinal.{u} :=
  stage.rho (D.map r) (D.point s)

theorem nativeImage_inaccessible (r : FiniteRowIndex a) (s : Nat) :
    stage.model.InternalInaccessible (stage.ordinal (D.nativeImage r s)) :=
  stage.rho_internalInaccessible (D.map r) (D.point_limit (rowEndpoint a r.val))
    (D.point_limit (r.val + 1)) (D.point_inaccessible (r.val + 1)) (D.point s) (D.point_inaccessible s)

theorem nativeImage_strictMonoOn (r : FiniteRowIndex a) :
    StrictMonoOn (D.nativeImage r) (Set.Iic (rowEndpoint a r.val)) := by
  obtain ⟨row, hr, he⟩ := finiteRow_endpoint_exists D.shapes r
  have endpoint := fromRight_le_last (D.valid _ _ hr).1 (D.valid _ _ hr).2.2.1
    (Row.step_pos (D.shapes row (rowAt_mem hr))) he
  intro i hi j hj less
  change i ≤ rowEndpoint a r.val at hi
  change j ≤ rowEndpoint a r.val at hj
  have oldBound : rowEndpoint a r.val ≤ a.length + 1 := by have := r.property.2; omega
  have pointLe (x : Nat) (bound : x ≤ rowEndpoint a r.val) : D.point x ≤ D.source r.val := by
    exact D.point_increasing.monotoneOn (by change x ≤ a.length + 1; omega)
      oldBound bound
  exact stage.rho_strictMonoOn (D.map r) (pointLe i hi) (pointLe j hj)
    (D.point_increasing (by change i ≤ a.length + 1; omega) (by change j ≤ a.length + 1; omega) less)

theorem nativeImage_predecessor (r : FiniteRowIndex a) {p : Nat} (pred : IBLP.predecessor a r.val = some p) :
    D.nativeImage r p = D.point r.val := by
  obtain ⟨row, hr, hp⟩ := Option.bind_eq_some_iff.mp pred
  exact (D.graph_represents r).read_ordinal_edge
    (D.edges r row hr (p, r.val) (Row.predecessor_edge (D.valid _ _ hr) (D.shapes row (rowAt_mem hr)) hp))

theorem nativeImage_endpoint (r : FiniteRowIndex a) :
    D.nativeImage r (rowEndpoint a r.val) = D.point (r.val + 1) :=
  stage.rho_of_source_le (D.map r) le_rfl

theorem nativeImage_gap (r : FiniteRowIndex a) {row : IBLP.Row} {p e s : Nat}
    (hr : IBLP.rowAt a r.val = some row) (hp : row.p = some p) (he : row.e = some e)
    (lower : p < s) (upper : s < e) :
    D.point r.val < D.nativeImage r s ∧ D.nativeImage r s < D.point (r.val + 1) := by
  have endpoint := rowEndpoint_eq hr he
  have pred : IBLP.predecessor a r.val = some p := by simp [IBLP.predecessor, hr, hp]
  constructor
  · rw [← D.nativeImage_predecessor r pred]
    apply D.nativeImage_strictMonoOn r
    · change p ≤ rowEndpoint a r.val; omega
    · change s ≤ rowEndpoint a r.val; omega
    · exact lower
  · rw [← D.nativeImage_endpoint r]
    apply D.nativeImage_strictMonoOn r
    · change s ≤ rowEndpoint a r.val; omega
    · change rowEndpoint a r.val ≤ rowEndpoint a r.val; rfl
    · omega

theorem nativeSource_image_gap (r : FiniteRowIndex a) {row : IBLP.Row} {p e : Nat} {sources : List Nat}
    (hr : IBLP.rowAt a r.val = some row) (hp : row.p = some p) (he : row.e = some e)
    (run : IBLP.nativeSources a r.val = some sources) :
    ∀ s ∈ sources, D.point r.val < D.nativeImage r s ∧ D.nativeImage r s < D.point (r.val + 1) := by
  intro s member
  have bounds := IBLP.nativeSources_bounds D.valid hr hp he run s member
  exact D.nativeImage_gap r hr hp he bounds.1 bounds.2

end IBLP.FiniteBoundedData
