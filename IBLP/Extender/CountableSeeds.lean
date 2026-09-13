import IBLP.Extender.ReadIndex

namespace IBLP.Extender.Derivation
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}

/-- The entire externally countable sequence of seeds is an actual graph
in M, and internal regularity bounds its rank strictly below beta. -/
noncomputable def countableSeed (inaccessible : stage.model.InternalInaccessible (stage.ordinal beta))
    (seeds : Nat → Seed stage beta) : Seed stage beta :=
  ⟨(stage.countableGraph (fun n => stage.rankInclude _ (seeds n))).val,
    (stage.countableGraph (fun n => stage.rankInclude _ (seeds n))).property,
    stage.countable_graph_rank_lt inaccessible _ (fun n => (seeds n).property.2)⟩

theorem project_countableSeed (D : Derivation stage alpha beta) (ha : Order.IsSuccLimit alpha)
    (inaccessible : stage.model.InternalInaccessible (stage.ordinal beta))
    (seeds : Nat → Seed stage beta) (n : Nat) :
    D.project (readIndex ha n) (countableSeed inaccessible seeds) = seeds n := by
  have hb : Order.IsSuccLimit beta := by
    simpa only [ModelStage.ordinal, Ordinal.rank_toZFSet] using
      stage.internalInaccessible_isSuccLimit (stage.ordinal beta) inaccessible
  let common := countableSeed inaccessible seeds
  let source : Test stage beta := ⟨common.val, common.property.1, common.property.2.trans (Order.lt_succ beta)⟩
  let target : Test stage beta := ⟨(seeds n).val, (seeds n).property.1,
    (seeds n).property.2.trans (Order.lt_succ beta)⟩
  have read : graphReadValue (n : Ordinal.{u}).toZFSet source.val target.val := by
    have h := stage.graphRead_satisfies (stage.ordinal (n : Ordinal.{u}))
      (stage.countableGraph (fun k => stage.rankInclude _ (seeds k)))
    rw [stage.graphRead_countableGraph] at h
    exact (graphReadRelation_absolute _ _ _ _).mp h
  have edge := (D.map_readIndex_edge_iff ha hb n source target).mpr
    ⟨(stage.mem_hierarchy beta common.val).mpr common.property, read⟩
  exact Subtype.ext (D.project_unique (readIndex ha n) common (seeds n).val edge).symm

theorem countable_directed (D : Derivation stage alpha beta) (ha : Order.IsSuccLimit alpha)
    (inaccessible : stage.model.InternalInaccessible (stage.ordinal beta))
    (seeds : Nat → Seed stage beta) :
    ∃ common : Seed stage beta, ∃ projections : Nat → IndexMap stage alpha,
      ∀ n, D.project (projections n) common = seeds n :=
  ⟨countableSeed inaccessible seeds, readIndex ha, D.project_countableSeed ha inaccessible seeds⟩

end IBLP.Extender.Derivation
