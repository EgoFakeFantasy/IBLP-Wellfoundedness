import IBLP.Model.HierarchyValueFormula
import IBLP.Model.SuccessorImage
import IBLP.Model.RankBridge

namespace IBLP.UniformDefinable
open FullMarkedBLP FirstOrder Language
universe u

theorem successor : UniformDefinable (fun (_ : ModelStage.{u}) (v : Fin 2 → _) =>
    (v 0).val = insert (v 1).val (v 1).val) :=
  (of_formula modelSuccessorFormula).congr (fun stage v => by
    have tuple : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
    rw [tuple, stage.model.successorFormula_realize]
    rfl)

theorem successor_hierarchy : UniformDefinable (fun (stage : ModelStage.{u}) (v : Fin 2 → _) =>
    ∃ beta : Ordinal.{u}, v 0 = stage.ordinal beta ∧ v 1 = stage.hierarchy (Order.succ beta)) := by
  have body := (ordinal.relabel ![(0 : Fin 3)]).and
    ((successor.relabel ![(2 : Fin 3), 0]).and (hierarchy_value.relabel ![(2 : Fin 3), 1]))
  refine body.exists_last.congr ?_
  intro stage v
  change (∃ s, ZFSet.IsOrdinal (v 0).val ∧ s.val = insert (v 0).val (v 0).val ∧
    ∃ gamma, s = stage.ordinal gamma ∧ v 1 = stage.hierarchy gamma) ↔ _
  constructor
  · rintro ⟨s, ordinal, hs, gamma, rfl, hv⟩
    have representation : v 0 = stage.ordinal (v 0).val.rank :=
      Subtype.ext ordinal.toZFSet_rank_eq.symm
    have same : gamma = Order.succ (v 0).val.rank := by
      rw [representation] at hs
      change gamma.toZFSet = insert ((v 0).val.rank.toZFSet) ((v 0).val.rank.toZFSet) at hs
      rw [← Ordinal.toZFSet_add_one] at hs
      exact Ordinal.toZFSet_injective hs
    exact ⟨(v 0).val.rank, representation, same ▸ hv⟩
  · rintro ⟨beta, h0, h1⟩
    refine ⟨stage.ordinal (Order.succ beta), ?_, ?_, Order.succ beta, rfl, h1⟩
    · rw [h0]; exact ZFSet.isOrdinal_toZFSet _
    · rw [h0]
      exact Ordinal.toZFSet_add_one beta

/-- Full elementarity of an actual graph between the successor rank sets
is a finite formula in the two ordinal endpoints and the graph itself. -/
theorem rank_graph : UniformDefinable (fun (stage : ModelStage.{u}) (v : Fin 3 → _) =>
    ∃ alpha beta : Ordinal.{u}, v 0 = stage.ordinal alpha ∧ v 1 = stage.ordinal beta ∧
      stage.InternalGraphElementary alpha beta (v 2)) := by
  have body := (successor_hierarchy.relabel ![(0 : Fin 5), 3]).and
    ((successor_hierarchy.relabel ![(1 : Fin 5), 4]).and
      (graph_elementary.relabel ![(3 : Fin 5), 4, 2]))
  refine body.exists_last.exists_last.congr ?_
  intro stage v
  change (∃ domain range, (∃ alpha, v 0 = stage.ordinal alpha ∧ domain = stage.hierarchy (Order.succ alpha)) ∧
    (∃ beta, v 1 = stage.ordinal beta ∧ range = stage.hierarchy (Order.succ beta)) ∧
      stage.model.GraphElementary (v 2) domain range) ↔ _
  constructor
  · rintro ⟨domain, range, ⟨alpha, ha, rfl⟩, ⟨beta, hb, rfl⟩, graph⟩
    exact ⟨alpha, beta, ha, hb, graph⟩
  · rintro ⟨alpha, beta, ha, hb, graph⟩
    exact ⟨stage.hierarchy (Order.succ alpha), stage.hierarchy (Order.succ beta),
      ⟨alpha, ha, rfl⟩, ⟨beta, hb, rfl⟩, graph⟩

end IBLP.UniformDefinable
