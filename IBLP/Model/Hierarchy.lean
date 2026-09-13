import IBLP.Model.HierarchyExistence

namespace IBLP
open FullMarkedBLP
universe u

theorem ModelStage.hierarchy_exists (stage : ModelStage.{u}) (beta : Ordinal.{u}) :
    ∃ value : stage.model.Element,
      (∀ z : ZFSet.{u}, z ∈ value.val ↔ z ∈ stage.model.carrier ∧ z.rank < beta) ∧
      value.val.rank = beta := by
  obtain ⟨range, graph, function, recursion⟩ :=
    stage.hierarchy_graph_exists (stage.ordinal (Order.succ beta)) (ZFSet.isOrdinal_toZFSet _)
  have member : (stage.ordinal beta).val ∈ (stage.ordinal (Order.succ beta)).val :=
    Ordinal.toZFSet_mem_toZFSet_iff.mpr (Order.lt_succ beta)
  obtain ⟨value, _, edge, _⟩ := function.2 (stage.ordinal beta) member
  refine ⟨value, ?_, ?_⟩
  · exact stage.model.hierarchyRec_mem_iff function (ZFSet.isOrdinal_toZFSet _) recursion beta
      (stage.ordinal beta) value rfl member edge
  · exact stage.model.hierarchyRec_value_rank function (ZFSet.isOrdinal_toZFSet _) recursion beta
      rfl member edge

/-- The actual set `V_beta^M`, constructed from a hierarchy graph inside M. -/
noncomputable def ModelStage.hierarchy (stage : ModelStage.{u}) (beta : Ordinal.{u}) :
    stage.model.Element := (stage.hierarchy_exists beta).choose

theorem ModelStage.mem_hierarchy (stage : ModelStage.{u}) (beta : Ordinal.{u}) (z : ZFSet.{u}) :
    z ∈ (stage.hierarchy beta).val ↔ z ∈ stage.model.carrier ∧ z.rank < beta :=
  (stage.hierarchy_exists beta).choose_spec.1 z

theorem ModelStage.hierarchy_rank (stage : ModelStage.{u}) (beta : Ordinal.{u}) :
    (stage.hierarchy beta).val.rank = beta := (stage.hierarchy_exists beta).choose_spec.2

theorem ModelStage.mem_hierarchy_iff (stage : ModelStage.{u}) (beta : Ordinal.{u})
    (z : stage.model.Element) : z.val ∈ (stage.hierarchy beta).val ↔ z.val.rank < beta := by
  rw [stage.mem_hierarchy]
  exact and_iff_right z.property

end IBLP
