import IBLP.Model.InternalRho
import IBLP.Model.BoundedHierarchyLevels

namespace IBLP
open FullMarkedBLP
universe u

namespace ModelStage

theorem rankIntersection_hierarchy (stage : ModelStage.{u}) {lambda : Ordinal.{u}}
    (x : stage.model.RankElement lambda) (eta : OrdinalDomain lambda) :
    stage.rankInclude lambda (stage.rankIntersection x (stage.rankHierarchy eta)) =
      stage.cutSpace.cut eta.val (stage.rankInclude lambda x) := by
  apply Subtype.ext
  change (stage.rankIntersection x (stage.rankHierarchy eta)).val = _
  rw [stage.rankIntersection_val, stage.rankHierarchy_val]
  apply ZFSet.ext
  intro w
  change (w ∈ x.val ∩ (stage.hierarchy eta.val).val) ↔ w ∈ x.val ∩ ZFSet.vonNeumann eta.val
  rw [ZFSet.mem_inter, ZFSet.mem_inter, stage.mem_hierarchy, ZFSet.mem_vonNeumann]
  exact ⟨fun h => ⟨h.1, h.2.2⟩,
    fun h => ⟨h.1, stage.model.transitive h.1 x.property.1, h.2⟩⟩

/-- Internal-model form of (3.6), on every model element. -/
theorem weakAction_cut_commute (stage : ModelStage.{u}) {alpha beta : Ordinal.{u}}
    (ha : Order.IsSuccLimit alpha) (k : stage.BoundedMap alpha beta)
    (eta : Ordinal.{u}) (z : stage.model.Element) :
    stage.weakAction k (stage.cutSpace.cut eta z) =
      stage.cutSpace.cut (stage.rho k eta) (stage.weakAction k z) := by
  have same : stage.rankCut alpha (stage.cutSpace.cut eta z) =
      stage.rankIntersection (stage.rankCut alpha z) (stage.rankHierarchy (clippedOrdinal alpha eta)) := by
    apply Subtype.ext
    rw [stage.rankCut_val, stage.rankIntersection_val, stage.rankCut_val, stage.rankHierarchy_val]
    apply ZFSet.ext
    intro w
    change (w ∈ (z.val ∩ ZFSet.vonNeumann eta) ∩ ZFSet.vonNeumann alpha) ↔
      w ∈ (z.val ∩ ZFSet.vonNeumann alpha) ∩ (stage.hierarchy (min alpha eta)).val
    simp only [ZFSet.mem_inter, ZFSet.mem_vonNeumann, stage.mem_hierarchy, lt_min_iff]
    have inside : w ∈ z.val → w ∈ stage.model.carrier := fun h => stage.model.transitive h z.property
    tauto
  unfold weakAction
  rw [same, stage.rankMap_intersection, stage.boundedMap_hierarchy ha, stage.rankIntersection_hierarchy]
  rfl

/-- Every algebraic field is derived from the actual internal elementary map. -/
noncomputable def boundedCutAction (stage : ModelStage.{u}) {alpha beta : Ordinal.{u}}
    (ha : Order.IsSuccLimit alpha) (k : stage.BoundedMap alpha beta) : CutAction stage.cutSpace where
  act := stage.weakAction k
  rho := stage.rho k
  bound := beta
  output_rank_le := stage.weakAction_rank_le k
  monotone := stage.rho_monotone k
  rho_le_bound := stage.rho_le k
  inflationary := stage.rho_inflationary k
  cut_commute := stage.weakAction_cut_commute ha k

end ModelStage
end IBLP
