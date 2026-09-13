import IBLP.Realization.NativeDomains
import IBLP.Model.RestrictionCritical

namespace IBLP.FiniteBoundedData
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (D : FiniteBoundedData stage a)
  (r : FiniteRowIndex a) {row : IBLP.Row} {p e : Nat} {sources : List Nat}
  (hr : IBLP.rowAt a r.val = some row) (hp : row.p = some p) (he : row.e = some e)
  (run : IBLP.nativeSources a r.val = some sources)

/-- The saved family graph is an actual internal subset of the old row graph. -/
noncomputable def nativeFamilyGraph (j : Nat) : stage.model.Element :=
  stage.boundedRestrictionGraph (D.graph r) (D.map r) (D.graph_represents r)
    (D.point (nativeDomainIndex r sources j)) (D.nativeDomain_point_le r hr hp he run j)

noncomputable def nativeFamilyMap (j : Nat) :
    stage.BoundedMap (D.point (nativeDomainIndex r sources j)) (D.nativeImage r (nativeDomainIndex r sources j)) :=
  stage.boundedRestrict (D.point_limit (rowEndpoint a r.val)) (D.map r)
    (D.point (nativeDomainIndex r sources j)) (D.nativeDomain_point_le r hr hp he run j)

theorem nativeFamilyGraph_represents (j : Nat) :
    stage.RepresentsBoundedMap (D.nativeFamilyGraph r hr hp he run j) (D.nativeFamilyMap r hr hp he run j) :=
  stage.boundedRestrictionGraph_represents (D.point_limit (rowEndpoint a r.val)) (D.graph r) (D.map r)
    (D.graph_represents r) (D.point (nativeDomainIndex r sources j)) (D.nativeDomain_point_le r hr hp he run j)

/-- Both source and target are exactly the named points for family row r+j,
including the original implicit endpoint at the top of the family. -/
theorem nativeFamilyGraph_elementary (j : Nat) (bound : j ≤ sources.length) :
    stage.InternalGraphElementary (D.nativePoint r sources (nativeDomainIndex r sources j))
      (D.nativePoint r sources (r.val + j + 1)) (D.nativeFamilyGraph r hr hp he run j) := by
  rw [D.nativeDomain_value r hr hp he run j, ← D.nativeDomain_image r sources j bound]
  exact (D.nativeFamilyGraph_represents r hr hp he run j).toInternalGraphElementary

theorem nativeFamilyGraph_edge_iff (j : Nat) (x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ (D.nativeFamilyGraph r hr hp he run j).val ↔
      x ∈ (stage.hierarchy (Order.succ (D.point (nativeDomainIndex r sources j)))).val ∧
      ZFSet.pair x y ∈ (D.graph r).val :=
  stage.boundedRestrictionGraph_edge_iff (D.graph r) (D.map r) (D.graph_represents r)
    (D.point (nativeDomainIndex r sources j)) (D.nativeDomain_point_le r hr hp he run j) x y

theorem nativeFamilyGraph_critical {c : Nat} (hm : row.columns.head? = some c) (j : Nat) :
    stage.model.GraphCriticalPoint (D.nativeFamilyGraph r hr hp he run j) (stage.ordinal (D.point c)) := by
  have cb := D.nativeDomainIndex_above_minimum r hr hp he hm run j
  have endpoint := D.nativeDomainIndex_le r hr hp he run j
  have eBound := fromRight_le_last (D.valid _ _ hr).1 (D.valid _ _ hr).2.2.1
    (Row.step_pos (D.shapes row (rowAt_mem hr))) he
  have exactEndpoint := rowEndpoint_eq hr he
  have sourceBound : nativeDomainIndex r sources j ≤ a.length + 1 := by have := r.property.2; omega
  apply stage.boundedRestrictionGraph_critical (D.point_limit (rowEndpoint a r.val)) (D.graph r) (D.map r)
    (D.graph_represents r) (D.point (nativeDomainIndex r sources j))
    (D.nativeDomain_point_le r hr hp he run j) (D.point c)
    (D.point_increasing.monotoneOn (by change c ≤ a.length + 1; omega) sourceBound cb)
    (D.critical r row c hr hm)

theorem nativeFamilyMap_restriction (j : Nat) :
    CutRestriction (stage.boundedCutAction (D.point_limit (nativeDomainIndex r sources j))
      (D.nativeFamilyMap r hr hp he run j))
      (stage.boundedCutAction (D.point_limit (rowEndpoint a r.val)) (D.map r)) :=
  stage.boundedRestrict_cutRestriction (D.point_limit (rowEndpoint a r.val))
    (D.point_limit (nativeDomainIndex r sources j)) (D.map r) (D.nativeDomain_point_le r hr hp he run j)

/-- The direct family-mark weak equality from (7.3), at the full natural
bound of the lower row, for every input of the internal model. -/
theorem nativeFamilyMap_allInputs (j k : Nat) (less : j < k) (bound : k ≤ sources.length) :
    CutAction.AllInputAgreement
      (stage.boundedCutAction (D.point_limit (nativeDomainIndex r sources k)) (D.nativeFamilyMap r hr hp he run k))
      (stage.boundedCutAction (D.point_limit (nativeDomainIndex r sources j)) (D.nativeFamilyMap r hr hp he run j))
      (D.nativePoint r sources (r.val + j + 1)) := by
  have hj := D.nativeFamilyMap_restriction r hr hp he run j
  have hk := D.nativeFamilyMap_restriction r hr hp he run k
  have targets : D.nativeImage r (nativeDomainIndex r sources j) ≤ D.nativeImage r (nativeDomainIndex r sources k) := by
    rw [D.nativeDomain_image r sources j (by omega), D.nativeDomain_image r sources k bound]
    exact (D.nativePoint_increasing r hr hp he run
      (by change r.val + j + 1 ≤ a.length + sources.length + 1; have := r.property.2; omega)
      (by change r.val + k + 1 ≤ a.length + sources.length + 1; have := r.property.2; omega) (by omega)).le
  rw [← D.nativeDomain_image r sources j (by omega)]
  intro z
  rw [hj.act_eq, hk.act_eq]
  change stage.cutSpace.cut (D.nativeImage r (nativeDomainIndex r sources j))
      (stage.cutSpace.cut (D.nativeImage r (nativeDomainIndex r sources k)) (stage.weakAction (D.map r) z)) =
    stage.cutSpace.cut (D.nativeImage r (nativeDomainIndex r sources j))
      (stage.cutSpace.cut (D.nativeImage r (nativeDomainIndex r sources j)) (stage.weakAction (D.map r) z))
  rw [stage.cutSpace.cut_lower targets, stage.cutSpace.cut_cut, min_self]

end IBLP.FiniteBoundedData
