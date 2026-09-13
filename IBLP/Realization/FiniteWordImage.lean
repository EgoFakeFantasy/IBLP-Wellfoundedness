import IBLP.Realization.FiniteDataImage
import IBLP.Model.CutActionImage

namespace IBLP
open FullMarkedBLP
universe u

theorem FiniteTraceRows.action_valid {stage : ModelStage.{u}} {a : Pattern}
    {theta : Fin (a.length + 2) → Ordinal.{u}} (R : FiniteTraceRows stage a theta) (r : FiniteRowIndex a) :
    R.toInternalTraceRows.actions.action r.val = stage.boundedCutAction (R.source_limit r) (R.map r) := by
  have general (row : Σ rho : Ordinal.{u}, stage.BoundedMap rho (finiteThetaExtension theta (r.val + 1)))
      (same : row = ⟨R.source r, R.map r⟩) (limit : Order.IsSuccLimit row.1) :
      stage.boundedCutAction limit row.2 = stage.boundedCutAction (R.source_limit r) (R.map r) := by
    subst row
    rfl
  exact general (R.extendedRow r.val) (R.extendedRow_valid r) (R.toInternalTraceRows.source_limit r.val)

namespace FiniteBoundedData
variable {source : ModelStage.{u}} {a : Pattern} (D : FiniteBoundedData source a)
  (target : ModelStage.{u}) (j : source.model.ElementaryMap target.model)

theorem rowAction_image (r : FiniteRowIndex a) :
    CutAction.Image j (source.ordinalImage j)
      (D.toFiniteTraceRows.toInternalTraceRows.actions.action r.val)
      ((D.image target j).toFiniteTraceRows.toInternalTraceRows.actions.action r.val) := by
  rw [D.toFiniteTraceRows.action_valid, (D.image target j).toFiniteTraceRows.action_valid]
  exact source.boundedCutAction_image target j (D.source r.val) (D.point (r.val + 1))
    (D.toFiniteTraceRows.source_limit r) (D.graph r) (D.elementary r)

theorem traceAction_image {paired start : Nat} {rows : List Nat} (h : FactorTrace a paired start rows) :
    CutAction.Image j (source.ordinalImage j)
      (h.word D.toFiniteTraceRows.toInternalTraceRows.actions)
      (h.word (D.image target j).toFiniteTraceRows.toInternalTraceRows.actions) := by
  induction h with
  | single hp hn => exact D.rowAction_image target j ⟨_, predecessor_row_index hp⟩
  | @cons r next tail hp hn inner ih =>
    rw [FactorTrace.word_cons D.toFiniteTraceRows.toInternalTraceRows.actions hp hn inner,
      FactorTrace.word_cons (D.image target j).toFiniteTraceRows.toInternalTraceRows.actions hp hn inner]
    exact (D.rowAction_image target j ⟨r, predecessor_row_index hp⟩).comp ih

theorem traceBound_image {paired start : Nat} {rows : List Nat} (h : FactorTrace a paired start rows) :
    (h.word (D.image target j).toFiniteTraceRows.toInternalTraceRows.actions).bound =
      source.ordinalImage j (h.word D.toFiniteTraceRows.toInternalTraceRows.actions).bound :=
  (D.traceAction_image target j h).bound

theorem traceSource_image {paired start : Nat} {rows : List Nat} (h : FactorTrace a paired start rows) :
    h.inputBound (D.image target j).toFiniteTraceRows.toInternalTraceRows.actions =
      source.ordinalImage j (h.inputBound D.toFiniteTraceRows.toInternalTraceRows.actions) := by
  let r : FiniteRowIndex a := ⟨rows.getLast h.nonempty, h.validRows _ (List.getLast_mem h.nonempty)⟩
  change (D.image target j).toFiniteTraceRows.toInternalTraceRows.source r.val =
    source.ordinalImage j (D.toFiniteTraceRows.toInternalTraceRows.source r.val)
  rw [(D.image target j).toFiniteTraceRows.source_valid, D.toFiniteTraceRows.source_valid]
  rfl

end FiniteBoundedData
end IBLP
