import IBLP.Realization.BoundedRealization
import IBLP.Realization.InitialCriticalPoint

namespace IBLP
open FullMarkedBLP
universe u

namespace RootGraphRealization
variable {lambda : Ordinal.{u}} {limit : Order.IsSuccLimit lambda}
  {theta : Nat → OrdinalDomain lambda} {graphs : Nat → RankDomain lambda}

/-- Reuse the very same six graphs and the original eight critical-sequence
points. No larger-rank hypothesis or new root pattern is introduced. -/
noncomputable def toFiniteBoundedData (h : RootGraphRealization limit theta graphs) :
    FiniteBoundedData initialStage root := by
  let points : Fin (root.length + 2) → Ordinal.{u} := fun i => (theta i.val).val
  have atPoint (i : Nat) (hi : i ≤ root.length + 1) :
      finiteThetaExtension points i = (theta i).val := by
    simp only [finiteThetaExtension, points, min_eq_left hi]
  refine {
    theta := points
    increasing := ?_
    inaccessible := fun i => h.internalInaccessible initialStage i.val
    valid := root_valid
    shapes := root_shapes
    graph := fun r => initialElement (graphs r.val).val
    elementary := ?_
    critical := ?_
    edges := ?_ }
  · intro i j smaller
    exact h.1 smaller
  · intro r
    obtain ⟨row, hr, he⟩ := finiteRow_endpoint_exists root_shapes r
    have endpointBound := fromRight_le_last (root_valid _ _ hr).1
      (root_valid _ _ hr).2.2.1 (Row.step_pos (root_shapes row (rowAt_mem hr))) he
    rw [atPoint _ (by omega), atPoint _ (by omega)]
    exact initialGraph_elementary limit (h.2.2.2 r.val row (rowEndpoint root r.val) hr he).1
  · intro r row minimum hr hm
    obtain ⟨selected, hselected, he⟩ := finiteRow_endpoint_exists root_shapes r
    have same := Option.some.inj (hselected.symm.trans hr)
    subst selected
    have endpointBound := fromRight_le_last (root_valid _ _ hr).1
      (root_valid _ _ hr).2.2.1 (Row.step_pos (root_shapes row (rowAt_mem hr))) he
    have minimumBound := root_minimum_le_endpoint hr he hm
    rw [atPoint _ (by omega)]
    exact (initial_graphCriticalPoint_iff _ _).mpr
      ((h.2.2.2 r.val row (rowEndpoint root r.val) hr he).2.1 minimum hm)
  · intro r row hr edge member
    obtain ⟨selected, hselected, he⟩ := finiteRow_endpoint_exists root_shapes r
    have same := Option.some.inj (hselected.symm.trans hr)
    subst selected
    obtain ⟨leftBound, rightBound⟩ := Row.edge_index_bounds (root_valid _ _ hr) member
    rw [atPoint _ (by omega), atPoint _ (by omega)]
    exact (graphApplies_absolute _ _ _).mp
      ((h.2.2.2 r.val row (rowEndpoint root r.val) hr he).2.2 edge member)

theorem toFiniteBoundedData_top (h : RootGraphRealization limit theta graphs) :
    h.toFiniteBoundedData.top = (theta 7).val := rfl

/-- Empty marks discharge only this particular root instance. The general
realization definition retains accurate trace and nontrivial weak certificates. -/
noncomputable def toBoundedRealization (h : RootGraphRealization limit theta graphs) :
    BoundedRealization initialStage root where
  data := h.toFiniteBoundedData
  proper := root_proper
  saturated := root_saturated
  marks := by
    intro r row b hr hb
    rw [root_marks_empty row (rowAt_mem hr)] at hb
    contradiction

theorem toBoundedRealization_top (h : RootGraphRealization limit theta graphs) :
    h.toBoundedRealization.top = (theta 7).val := rfl

end RootGraphRealization

/-- Section 9 supplies the complete section-3 finite semantic realization
from precisely the original nontrivial I3 rank self-embedding assumption. -/
theorem exists_bounded_root_of_i3 (h : I3.{u}) :
    Nonempty (BoundedRealization initialStage.{u} root) := by
  obtain ⟨lambda, limit, theta, graphs, realized⟩ := exists_root_graphs_of_i3 h
  exact ⟨realized.toBoundedRealization⟩

end IBLP
