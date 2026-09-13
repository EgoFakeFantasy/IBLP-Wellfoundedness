import IBLP.Model.FiniteSets
import IBLP.Model.Graph
import FullMarkedBLP.RankFiniteAssignment

namespace IBLP
open FullMarkedBLP
universe u

theorem ModelStage.finiteGraph_function (stage : ModelStage.{u}) {n : Nat}
    (values : Fin n → stage.model.Element) :
    ZFSet.IsFunc (n : Ordinal.{u}).toZFSet (stage.finiteRange values).val
      (stage.finiteGraph values).val := by
  constructor
  · intro p hp
    rw [stage.finiteGraph_val, ZFSet.mem_range] at hp
    obtain ⟨i, rfl⟩ := hp
    exact ZFSet.pair_mem_prod.mpr ⟨(finZFSetEquiv n i).property,
      by rw [stage.finiteRange_val]; exact ZFSet.mem_range.mpr ⟨i, rfl⟩⟩
  · intro a ha
    let i := (finZFSetEquiv n).symm ⟨a, ha⟩
    have ei : (i.val : Ordinal.{u}).toZFSet = a :=
      congrArg Subtype.val ((finZFSetEquiv n).apply_symm_apply ⟨a, ha⟩)
    refine ⟨(values i).val, (stage.finiteGraph_edge_iff values a _).mpr ⟨i, ei, rfl⟩, ?_⟩
    intro b hb
    obtain ⟨j, ej, hj⟩ := (stage.finiteGraph_edge_iff values a b).mp hb
    have ji : j = i := Fin.ext (Nat.cast_injective (Ordinal.toZFSet_injective (ej.trans ei.symm)))
    simpa only [ji] using hj.symm

theorem ModelStage.finiteGraph_injective (stage : ModelStage.{u}) {n : Nat} :
    Function.Injective (stage.finiteGraph (n := n)) := by
  intro v w eq
  funext i
  have edge := (stage.finiteGraph_edge_iff v _ _).mpr ⟨i, rfl, rfl⟩
  rw [eq] at edge
  obtain ⟨j, hj, hv⟩ := (stage.finiteGraph_edge_iff w _ _).mp edge
  have ji : j = i := Fin.ext (Nat.cast_injective (Ordinal.toZFSet_injective hj))
  exact Subtype.ext (by simpa only [ji] using hv.symm)

theorem ModelStage.finiteRange_rank_lt (stage : ModelStage.{u}) {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {n : Nat} (values : Fin n → stage.model.Element)
    (small : ∀ i, (values i).val.rank < lambda) :
    (stage.finiteRange values).val.rank < lambda := by
  rw [stage.finiteRange_val]
  exact rankFiniteRange_bound hl (fun i => ⟨(values i).val, small i⟩)

theorem ModelStage.finiteGraph_rank_lt (stage : ModelStage.{u}) {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {n : Nat} (values : Fin n → stage.model.Element)
    (small : ∀ i, (values i).val.rank < lambda) :
    (stage.finiteGraph values).val.rank < lambda := by
  refine rank_function_lt_of_limit hl ?_ ?_ (stage.finiteGraph_function values)
  · simpa only [Ordinal.rank_toZFSet] using Ordinal.natCast_lt_of_isSuccLimit hl n
  · exact stage.finiteRange_rank_lt hl values small

theorem ModelStage.finiteGraph_eq_rankAssignment (stage : ModelStage.{u})
    {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda) {n : Nat}
    (values : Fin n → stage.model.Element) (small : ∀ i, (values i).val.rank < lambda) :
    (stage.finiteGraph values).val =
      (rankAssignment hl (fun i => ⟨(values i).val, small i⟩)).val := by
  apply ZFSet.ext
  intro p
  rw [stage.finiteGraph_val, ZFSet.mem_range, rankAssignment_mem_iff]
  simp only [eq_comm]

end IBLP
