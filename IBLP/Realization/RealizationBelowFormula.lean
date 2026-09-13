import IBLP.Realization.CompletePayloadFormula
import IBLP.Realization.BelowFormulaReflection

namespace IBLP
open FullMarkedBLP
universe u

theorem UniformDefinable.complete_below_witnesses (a : Pattern) :
    UniformDefinable (fun (stage : ModelStage.{u}) (v : Fin 1 → _) =>
      ∃ points : Fin (a.length + 2) → stage.model.Element,
      ∃ graphs : Fin a.length → stage.model.Element,
        CompletePayload stage a points (graphs ∘ (finiteRowEquiv a).symm) ∧
        (points ⟨a.length + 1, by omega⟩).val ∈ (v 0).val) := by
  let points : Fin (a.length + 2) → Fin (1 + (a.length + 2) + a.length) :=
    fun i => (Fin.natAdd 1 i).castAdd a.length
  let graphs : FiniteRowIndex a → Fin (1 + (a.length + 2) + a.length) :=
    fun r => Fin.natAdd (1 + (a.length + 2)) ((finiteRowEquiv a).symm r)
  let bound : Fin (1 + (a.length + 2) + a.length) :=
    (Fin.castAdd (a.length + 2) (0 : Fin 1)).castAdd a.length
  have body := (complete_payload a points graphs).and (member (points ⟨a.length + 1, by omega⟩) bound)
  refine (exists_fin (a.length + 2) (exists_fin a.length body)).congr ?_
  intro stage v
  apply exists_congr
  intro ps
  apply exists_congr
  intro gs
  have pointValues : Fin.append (Fin.append v ps) gs ∘ points = ps := by
    funext i; simp [points]
  have graphValues : Fin.append (Fin.append v ps) gs ∘ graphs = gs ∘ (finiteRowEquiv a).symm := by
    funext i; simp [graphs]
  rw [pointValues, graphValues]
  simp only [points, bound, Fin.append_left, Fin.append_right]

/-- For every fixed original finite pattern, one actual finite membership
formula expresses existence of its full saturated realization below the
given ordinal. All syntax, row graphs and weak mark clauses are decoded. -/
theorem UniformDefinable.realization_below (a : Pattern) :
    UniformDefinable (realizationBelowPredicate.{u} a) := by
  refine (ordinal.and (complete_below_witnesses a)).congr ?_
  intro stage v
  change (_ ∧ _) ↔ ZFSet.IsOrdinal (v 0).val ∧ RealizationBelow stage a (v 0).val.rank
  apply and_congr_right
  intro ordinal
  have boundEq : v 0 = stage.ordinal (v 0).val.rank := Subtype.ext ordinal.toZFSet_rank_eq.symm
  constructor
  · rintro ⟨points, graphs, payload, smaller⟩
    refine ⟨payload.decode, ?_⟩
    have topEq : stage.ordinal payload.decode.top = points ⟨a.length + 1, by omega⟩ :=
      payload.decode_points _
    rw [← topEq, boundEq] at smaller
    exact Ordinal.toZFSet_mem_toZFSet_iff.mp smaller
  · rintro ⟨R, smaller⟩
    refine ⟨fun i => stage.ordinal (R.data.theta i), fun i => R.data.graph (finiteRowEquiv a i), ?_, ?_⟩
    · have graphsEq : (fun i => R.data.graph (finiteRowEquiv a i)) ∘ (finiteRowEquiv a).symm = R.data.graph := by
        funext r; simp
      rw [graphsEq]
      exact R.completePayload
    · rw [boundEq]
      exact Ordinal.toZFSet_mem_toZFSet_iff.mpr smaller

end IBLP
