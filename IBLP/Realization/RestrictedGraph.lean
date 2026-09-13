import IBLP.Realization.BoundedMapGraph
import IBLP.Model.InternalRestrictionAlgebra

namespace IBLP
open FullMarkedBLP
universe u

namespace ModelStage

theorem representsBoundedMap_of_edges (stage : ModelStage.{u}) {alpha beta : Ordinal.{u}}
    (graph : stage.model.Element) (k : stage.BoundedMap alpha beta) (range : ZFSet.{u})
    (function : ZFSet.IsFunc (stage.hierarchy (Order.succ alpha)).val range graph.val)
    (edges : ∀ x, ZFSet.pair x.val (k x).val ∈ graph.val) : stage.RepresentsBoundedMap graph k := by
  refine ⟨isFunc_retarget function ?_, edges⟩
  intro a b edge
  have ha := (ZFSet.pair_mem_prod.mp (function.1 edge)).1
  let x : stage.model.RankElement (Order.succ alpha) := ⟨a, (stage.mem_hierarchy _ a).mp ha⟩
  have same : b = (k x).val := (function.2 a ha).unique edge (edges x)
  rw [same]
  exact (stage.mem_hierarchy _ _).mpr (k x).property

/-- The restriction is a set belonging to M, constructed by a finite formula. -/
noncomputable def boundedRestrictionGraph (stage : ModelStage.{u}) {alpha beta : Ordinal.{u}}
    (graph : stage.model.Element) (k : stage.BoundedMap alpha beta)
    (represents : stage.RepresentsBoundedMap graph k) (delta : Ordinal.{u}) (included : delta ≤ alpha) :
    stage.model.Element := stage.restrictGraph graph (stage.hierarchy (Order.succ alpha))
      (stage.hierarchy (Order.succ beta)) (stage.hierarchy (Order.succ delta)) represents.1
      (stage.hierarchy_mono (Order.succ_le_succ included))

theorem boundedRestrictionGraph_edge_iff (stage : ModelStage.{u}) {alpha beta : Ordinal.{u}}
    (graph : stage.model.Element) (k : stage.BoundedMap alpha beta)
    (represents : stage.RepresentsBoundedMap graph k) (delta : Ordinal.{u}) (included : delta ≤ alpha)
    (x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ (stage.boundedRestrictionGraph graph k represents delta included).val ↔
      x ∈ (stage.hierarchy (Order.succ delta)).val ∧ ZFSet.pair x y ∈ graph.val :=
  stage.restrictGraph_edge_iff graph _ _ _ represents.1 _ x y

theorem boundedRestrictionGraph_represents (stage : ModelStage.{u}) {alpha beta : Ordinal.{u}}
    (ha : Order.IsSuccLimit alpha) (graph : stage.model.Element) (k : stage.BoundedMap alpha beta)
    (represents : stage.RepresentsBoundedMap graph k) (delta : Ordinal.{u}) (included : delta ≤ alpha) :
    stage.RepresentsBoundedMap (stage.boundedRestrictionGraph graph k represents delta included)
      (stage.boundedRestrict ha k delta included) := by
  apply stage.representsBoundedMap_of_edges _ _ (stage.hierarchy (Order.succ beta)).val
    (stage.restrictGraph_function graph _ _ _ represents.1 _)
  intro x
  apply (stage.boundedRestrictionGraph_edge_iff graph k represents delta included _ _).mpr
  rw [stage.boundedRestrict_val]
  exact ⟨(stage.mem_hierarchy _ _).mpr x.property,
    represents.2 (stage.rankLift (Order.succ_le_succ included) x)⟩

theorem boundedRestrictionGraph_elementary (stage : ModelStage.{u}) {alpha beta : Ordinal.{u}}
    (ha : Order.IsSuccLimit alpha) (graph : stage.model.Element) (k : stage.BoundedMap alpha beta)
    (represents : stage.RepresentsBoundedMap graph k) (delta : Ordinal.{u}) (included : delta ≤ alpha) :
    stage.InternalGraphElementary delta (stage.rho k delta)
      (stage.boundedRestrictionGraph graph k represents delta included) :=
  (stage.boundedRestrictionGraph_represents ha graph k represents delta included).toInternalGraphElementary

end ModelStage
end IBLP
