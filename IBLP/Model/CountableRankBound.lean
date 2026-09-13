import IBLP.Model.CountableImage
import IBLP.Model.InaccessibleAmbient

namespace IBLP.ModelStage
open FullMarkedBLP
universe u

/-- Internal regularity bounds every external countable ordinal sequence:
the maintained external closure puts its complete graph inside the model. -/
theorem countable_ordinal_bound (stage : ModelStage.{u}) {beta : Ordinal.{u}}
    (uncountable : stage.model.InternalUncountable (stage.ordinal beta))
    (regular : stage.model.NoSmallCofinal (stage.ordinal beta))
    (f : Nat → Ordinal.{u}) (bounded : ∀ n, f n < beta) :
    ∃ delta < beta, ∀ n, f n ≤ delta := by
  classical
  by_contra! cofinal
  let values : Nat → stage.model.Element := fun n => stage.ordinal (f n)
  let graph := stage.countableGraph values
  have function : ZFSet.IsFunc Ordinal.omega0.toZFSet beta.toZFSet graph.val := by
    refine ⟨?_, (stage.countableGraph_function values).2⟩
    intro p hp
    obtain ⟨n, rfl⟩ := ZFSet.mem_range.mp hp
    exact ZFSet.pair_mem_prod.mpr
      ⟨(natZFSetOmegaEquiv n).property, Ordinal.toZFSet_mem_toZFSet_iff.mpr (bounded n)⟩
  apply regular (stage.ordinal Ordinal.omega0)
    ((stage.model.internalUncountable_iff _).mp uncountable) graph
  refine ⟨function, ?_⟩
  intro b hb
  obtain ⟨delta, hd, rep⟩ := Ordinal.mem_toZFSet_iff.mp hb
  obtain ⟨n, hn⟩ := cofinal delta hd
  refine ⟨(n : Ordinal.{u}).toZFSet, (natZFSetOmegaEquiv n).property,
    (f n).toZFSet, Ordinal.toZFSet_mem_toZFSet_iff.mpr (bounded n),
    ZFSet.mem_range.mpr ⟨n, rfl⟩, ?_⟩
  rw [← rep]
  exact Ordinal.toZFSet_mem_toZFSet_iff.mpr hn

theorem countable_range_rank_lt (stage : ModelStage.{u}) {beta : Ordinal.{u}}
    (inaccessible : stage.model.InternalInaccessible (stage.ordinal beta))
    (f : Nat → stage.model.Element) (bounded : ∀ n, (f n).val.rank < beta) :
    (stage.countableRange f).val.rank < beta := by
  have limit : Order.IsSuccLimit beta := by
    simpa only [ModelStage.ordinal, Ordinal.rank_toZFSet] using
      stage.internalInaccessible_isSuccLimit (stage.ordinal beta) inaccessible
  obtain ⟨delta, hd, h⟩ := stage.countable_ordinal_bound inaccessible.2.1 inaccessible.2.2.1
    (fun n => (f n).val.rank) bounded
  apply lt_of_le_of_lt _ (limit.succ_lt hd)
  apply ZFSet.rank_le_iff.mpr
  intro x hx
  obtain ⟨n, rfl⟩ := ZFSet.mem_range.mp hx
  exact (h n).trans_lt (Order.lt_succ delta)

theorem countable_graph_rank_lt (stage : ModelStage.{u}) {beta : Ordinal.{u}}
    (inaccessible : stage.model.InternalInaccessible (stage.ordinal beta))
    (f : Nat → stage.model.Element) (bounded : ∀ n, (f n).val.rank < beta) :
    (stage.countableGraph f).val.rank < beta := by
  have limit : Order.IsSuccLimit beta := by
    simpa only [ModelStage.ordinal, Ordinal.rank_toZFSet] using
      stage.internalInaccessible_isSuccLimit (stage.ordinal beta) inaccessible
  have omegaBelow : Ordinal.omega0 < beta :=
    Ordinal.toZFSet_mem_toZFSet_iff.mp ((stage.model.internalUncountable_iff _).mp inaccessible.2.1)
  let pairs : Nat → stage.model.Element := fun n => stage.orderedPair (stage.ordinal (n : Ordinal.{u})) (f n)
  have pairBound (n : Nat) : (pairs n).val.rank < beta := by
    change (stage.orderedPair _ _).val.rank < beta
    rw [stage.orderedPair_val]
    apply rank_orderedPair_lt_of_limit limit _ (bounded n)
    simpa only [ModelStage.ordinal, Ordinal.rank_toZFSet] using (Ordinal.natCast_lt_omega0 n).trans omegaBelow
  have rankBound := stage.countable_range_rank_lt inaccessible pairs pairBound
  have same : (stage.countableRange pairs).val = (stage.countableGraph f).val := by
    apply congrArg ZFSet.range
    funext n
    exact stage.orderedPair_val _ _
  rwa [same] at rankBound

end IBLP.ModelStage
