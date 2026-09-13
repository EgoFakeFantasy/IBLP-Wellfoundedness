import IBLP.Realization.TraceGraphImage
import IBLP.Realization.MarkFormula

namespace IBLP
open FullMarkedBLP
universe u
namespace FiniteBoundedData
variable {source : ModelStage.{u}} {a : Pattern} (D : FiniteBoundedData source a)
  (target : ModelStage.{u}) (j : source.model.ElementaryMap target.model)

theorem markFormulaParameters_image (r : FiniteRowIndex a)
    {paired start : Nat} {rows : List Nat} (h : FactorTrace a paired start rows) :
    (D.image target j).markFormulaParameters r h = j ∘ D.markFormulaParameters r h := by
  funext i
  fin_cases i
  · rfl
  · exact D.traceGraph_image target j h
  · exact (source.hierarchy_image target j (D.source r.val)).symm
  · change target.hierarchy (h.inputBound (D.image target j).toFiniteTraceRows.toInternalTraceRows.actions) = _
    rw [D.traceSource_image target j]
    exact (source.hierarchy_image target j _).symm
  · change target.hierarchy (h.word (D.image target j).toFiniteTraceRows.toInternalTraceRows.actions).bound = _
    rw [D.traceBound_image target j]
    exact (source.hierarchy_image target j _).symm

theorem markCertificate_image (r : FiniteRowIndex a)
    {paired start : Nat} {rows : List Nat} (h : FactorTrace a paired start rows) :
    h.MarkCertificate (D.image target j).toFiniteTraceRows.toInternalTraceRows r.val ↔
      h.MarkCertificate D.toFiniteTraceRows.toInternalTraceRows r.val := by
  have image := j.map_formula modelWeakAgreementFormula (D.markFormulaParameters r h)
  rw [← D.markFormulaParameters_image target j, D.markFormula_realize,
    (D.image target j).markFormula_realize] at image
  exact image

theorem markRealized_image (r : FiniteRowIndex a) (row : Row) (b : Nat) :
    (D.image target j).MarkRealized r.val row b ↔ D.MarkRealized r.val row b := by
  unfold MarkRealized
  constructor
  · rintro ⟨paired, trace, sourceIndex, computed, h, certificate⟩
    exact ⟨paired, trace, sourceIndex, computed, h, (D.markCertificate_image target j r h).mp certificate⟩
  · rintro ⟨paired, trace, sourceIndex, computed, h, certificate⟩
    exact ⟨paired, trace, sourceIndex, computed, h, (D.markCertificate_image target j r h).mpr certificate⟩

end FiniteBoundedData

namespace BoundedRealization
variable {source : ModelStage.{u}} {a : Pattern}

/-- The same finite pattern, with every point, graph, precise trace and
full mark certificate transported by the actual elementary map. -/
noncomputable def image (R : BoundedRealization source a) (target : ModelStage.{u})
    (j : source.model.ElementaryMap target.model) : BoundedRealization target a where
  data := R.data.image target j
  proper := R.proper
  saturated := R.saturated
  marks := by
    intro r row b hr hb
    exact (R.data.markRealized_image target j ⟨r, rowAt_pos hr, rowAt_le_length hr⟩ row b).mpr (R.marks r row b hr hb)

theorem image_top (R : BoundedRealization source a) (target : ModelStage.{u})
    (j : source.model.ElementaryMap target.model) :
    (R.image target j).top = source.ordinalImage j R.top := rfl

end BoundedRealization
end IBLP
