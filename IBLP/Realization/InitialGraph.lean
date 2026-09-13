import IBLP.Realization.BoundedMapGraph
import IBLP.Rank.GraphAbsoluteness
import IBLP.Rank.RootGraphs
import IBLP.Realization.RootInaccessible

namespace IBLP
open FullMarkedBLP FirstOrder Language
universe u

def initialElement (z : ZFSet.{u}) : initialStage.{u}.model.Element := ⟨z, Set.mem_univ _⟩

def initialRankEquiv (alpha : Ordinal.{u}) :
    Language.Equiv membershipLanguage (initialStage.model.RankElement alpha) (RankDomain alpha) where
  toFun := fun x => ⟨x.val, x.property.2⟩
  invFun := fun x => ⟨x.val, Set.mem_univ _, x.property⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_fun' := fun f => Empty.elim f
  map_rel' := by
    intro n r values
    obtain ⟨same⟩ := r
    subst n
    rfl

theorem initialStage_hierarchy (alpha : Ordinal.{u}) :
    (initialStage.hierarchy alpha).val = ZFSet.vonNeumann alpha := by
  apply ZFSet.ext
  intro x
  rw [initialStage.mem_hierarchy, ZFSet.mem_vonNeumann]
  exact and_iff_right (Set.mem_univ _)

/-- The old ambient graph and the new initial internal graph are the same
actual set, interpreted in equivalent full membership structures. -/
theorem initialGraph_elementary {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {graph : RankDomain lambda} {alpha beta : OrdinalDomain lambda}
    (h : GraphElementary graph (ordinalSuccessor hl alpha) (ordinalSuccessor hl beta)) :
    initialStage.InternalGraphElementary alpha.val beta.val (initialElement graph.val) := by
  let k : initialStage.BoundedMap alpha.val beta.val :=
    (initialRankEquiv (Order.succ beta.val)).symm.toElementaryEmbedding.comp
      (h.toEmbedding.comp (initialRankEquiv (Order.succ alpha.val)).toElementaryEmbedding)
  have represents : initialStage.RepresentsBoundedMap (initialElement graph.val) k := by
    constructor
    · rw [initialStage_hierarchy, initialStage_hierarchy]
      exact (function_absolute _ _ _).mp h.1
    · intro x
      exact (graphApplies_absolute _ _ _).mp
        (h.value_applies (initialRankEquiv (Order.succ alpha.val) x))
  exact represents.toInternalGraphElementary

/-- This retains all original root data, including critical points and every
row edge, while interpreting the very same six graphs internally. -/
theorem exists_initial_root_internal_graphs_of_i3 (h : I3.{u}) :
    ∃ (lambda : Ordinal.{u}) (hl : Order.IsSuccLimit lambda)
      (theta : Nat → OrdinalDomain lambda) (graphs : Nat → RankDomain lambda),
      RootGraphRealization hl theta graphs ∧
      ∀ r row e, rowAt root r = some row → row.e = some e →
        initialStage.InternalGraphElementary (theta e).val (theta (r + 1)).val
          (initialElement (graphs r).val) := by
  obtain ⟨lambda, hl, theta, graphs, realized⟩ := exists_root_graphs_of_i3 h
  refine ⟨lambda, hl, theta, graphs, realized, ?_⟩
  intro r row e hr he
  exact initialGraph_elementary hl (realized.2.2.2 r row e hr he).1

/-- One common witness supplies the original root realization, the internal
inaccessible points and all six full successor-rank elementary set graphs. -/
theorem exists_initial_root_realization_of_i3 (h : I3.{u}) :
    ∃ (lambda : Ordinal.{u}) (hl : Order.IsSuccLimit lambda)
      (theta : Nat → OrdinalDomain lambda) (graphs : Nat → RankDomain lambda),
      RootGraphRealization hl theta graphs ∧
      (∀ i, initialStage.model.InternalInaccessible (initialStage.ordinal (theta i).val)) ∧
      ∀ r row e, rowAt root r = some row → row.e = some e →
        initialStage.InternalGraphElementary (theta e).val (theta (r + 1)).val
          (initialElement (graphs r).val) := by
  obtain ⟨lambda, hl, theta, graphs, realized, internalGraphs⟩ := exists_initial_root_internal_graphs_of_i3 h
  exact ⟨lambda, hl, theta, graphs, realized, realized.internalInaccessible initialStage, internalGraphs⟩

end IBLP
