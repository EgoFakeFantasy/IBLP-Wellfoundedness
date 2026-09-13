import IBLP.Realization.GraphWordFormula
import IBLP.Realization.MarkFormula
import IBLP.Model.HierarchyValueFormula

namespace IBLP
open FullMarkedBLP FirstOrder Language
universe u

def TraceCertificatePayload (stage : ModelStage.{u}) (graphs : Nat → stage.model.Element)
    (rows : List Nat) (carrier source input : stage.model.Element) : Prop :=
  ∃ w : Fin 5 → stage.model.Element,
    GraphWord stage graphs rows (w 0) ∧
    (∃ beta : Ordinal.{u}, source = stage.ordinal beta ∧ w 2 = stage.hierarchy beta) ∧
    (∃ beta : Ordinal.{u}, input = stage.ordinal beta ∧ w 3 = stage.hierarchy beta) ∧
    (∃ beta : Ordinal.{u}, w 1 = stage.ordinal beta ∧ w 4 = stage.hierarchy beta) ∧
    ZFSet.pair input.val (w 1).val ∈ (w 0).val ∧
    modelWeakAgreementFormula.Realize ![carrier, w 0, w 2, w 3, w 4]

theorem UniformDefinable.trace_certificate (rows : List Nat) {n : Nat}
    (graphs : Nat → Fin n) (carrier source input : Fin n) :
    UniformDefinable (fun (stage : ModelStage.{u}) v =>
      TraceCertificatePayload stage (v ∘ graphs) rows (v carrier) (v source) (v input)) := by
  let w : Fin 5 → Fin (n + 5) := Fin.natAdd n
  have word := graph_word rows (fun r => (graphs r).castAdd 5) (w 0)
  have sourceRank := hierarchy_value.relabel ![source.castAdd 5, w 2]
  have inputRank := hierarchy_value.relabel ![input.castAdd 5, w 3]
  have boundRank := hierarchy_value.relabel ![w 1, w 4]
  have edge := graph_edge.relabel ![w 0, input.castAdd 5, w 1]
  have weak := (of_formula modelWeakAgreementFormula).relabel
    ![carrier.castAdd 5, w 0, w 2, w 3, w 4]
  refine (exists_fin 5 (word.and (sourceRank.and (inputRank.and (boundRank.and (edge.and weak)))))).congr ?_
  intro stage v
  unfold TraceCertificatePayload
  apply exists_congr
  intro witnesses
  have factors : Fin.append v witnesses ∘ (fun r => (graphs r).castAdd 5) = v ∘ graphs := by
    funext r; simp
  have weakTuple : Fin.append v witnesses ∘ ![carrier.castAdd 5, w 0, w 2, w 3, w 4] =
      ![v carrier, witnesses 0, witnesses 2, witnesses 3, witnesses 4] := by
    funext i; fin_cases i <;> simp [w]
  rw [factors, weakTuple]
  simp only [Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_succ, Fin.append_left, Fin.append_right, w]

theorem ModelStage.ordinal_hierarchy_iff (stage : ModelStage.{u}) (alpha : Ordinal.{u})
    (value : stage.model.Element) :
    (∃ beta : Ordinal.{u}, stage.ordinal alpha = stage.ordinal beta ∧ value = stage.hierarchy beta) ↔
      value = stage.hierarchy alpha := by
  constructor
  · rintro ⟨beta, same, value⟩
    have equal : alpha = beta := Ordinal.toZFSet_injective (congrArg Subtype.val same)
    exact equal.symm ▸ value
  · intro h; exact ⟨alpha, rfl, h⟩

namespace FiniteBoundedData
variable {stage : ModelStage.{u}} {a : Pattern} (D : FiniteBoundedData stage a)

theorem traceGraph_endpoint_iff {target start : Nat} {rows : List Nat} (h : FactorTrace a target start rows)
    (value : stage.model.Element) :
    ZFSet.pair (h.inputBound D.toFiniteTraceRows.toInternalTraceRows.actions).toZFSet value.val ∈
      (D.traceGraph h).val ↔ value = stage.ordinal (h.word D.toFiniteTraceRows.toInternalTraceRows.actions).bound := by
  unfold traceGraph
  rw [h.internalCompositeGraph_exact D.toFiniteTraceRows.toInternalTraceRows (D.graphs_on_trace h)]
  constructor
  · rintro ⟨x, hx, hy⟩
    have same : x = stage.rankOrdinal (endpoint (h.inputBound D.toFiniteTraceRows.toInternalTraceRows.actions)) :=
      Subtype.ext hx
    rw [same, h.internalComposite_endpoint D.toFiniteTraceRows.toInternalTraceRows] at hy
    exact Subtype.ext hy.symm
  · intro same
    exact ⟨stage.rankOrdinal (endpoint (h.inputBound D.toFiniteTraceRows.toInternalTraceRows.actions)),
      rfl, (h.internalComposite_endpoint D.toFiniteTraceRows.toInternalTraceRows).trans
        (congrArg Subtype.val same).symm⟩

/-- The finite witness includes the exact computed natural top of the
history word, so it expresses the original full weak certificate. -/
theorem traceCertificatePayload_iff (r : FiniteRowIndex a)
    {target start : Nat} {rows : List Nat} (h : FactorTrace a target start rows)
    (graphs : Nat → stage.model.Element) (saved : ∀ i : FiniteRowIndex a, graphs i.val = D.graph i) :
    TraceCertificatePayload stage graphs rows (D.graph r) (stage.ordinal (D.source r.val))
      (stage.ordinal (h.inputBound D.toFiniteTraceRows.toInternalTraceRows.actions)) ↔
      h.MarkCertificate D.toFiniteTraceRows.toInternalTraceRows r.val := by
  unfold TraceCertificatePayload
  constructor
  · rintro ⟨w, word, sourceRank, inputRank, boundRank, edge, weak⟩
    have wordEq := (D.graphWord_iff h graphs saved _).mp word
    have sourceEq := (stage.ordinal_hierarchy_iff _ _).mp sourceRank
    have inputEq := (stage.ordinal_hierarchy_iff _ _).mp inputRank
    rw [wordEq] at edge
    have boundEq := (D.traceGraph_endpoint_iff h _).mp edge
    rw [boundEq] at boundRank
    have boundRankEq := (stage.ordinal_hierarchy_iff _ _).mp boundRank
    rw [wordEq, sourceEq, inputEq, boundRankEq] at weak
    exact (D.markFormula_realize r h).mp weak
  · intro certificate
    refine ⟨![D.traceGraph h, stage.ordinal (h.word D.toFiniteTraceRows.toInternalTraceRows.actions).bound,
      stage.hierarchy (D.source r.val), stage.hierarchy (h.inputBound D.toFiniteTraceRows.toInternalTraceRows.actions),
      stage.hierarchy (h.word D.toFiniteTraceRows.toInternalTraceRows.actions).bound], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (D.graphWord_iff h graphs saved _).mpr rfl
    · exact ⟨_, rfl, rfl⟩
    · exact ⟨_, rfl, rfl⟩
    · exact ⟨_, rfl, rfl⟩
    · exact (D.traceGraph_endpoint_iff h _).mpr rfl
    · exact (D.markFormula_realize r h).mpr certificate

end FiniteBoundedData
end IBLP
