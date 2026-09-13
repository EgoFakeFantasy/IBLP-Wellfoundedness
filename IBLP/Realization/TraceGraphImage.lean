import IBLP.Realization.FiniteWordImage
import IBLP.Realization.CompositeGraphEquations

namespace IBLP.FiniteBoundedData
open FullMarkedBLP
universe u
variable {source : ModelStage.{u}} {a : Pattern} (D : FiniteBoundedData source a)

noncomputable def traceGraph {paired start : Nat} {rows : List Nat} (h : FactorTrace a paired start rows) :
    source.model.Element := h.internalCompositeGraph D.toFiniteTraceRows.toInternalTraceRows (D.graphs_on_trace h)

theorem traceGraph_elementary {paired start : Nat} {rows : List Nat} (h : FactorTrace a paired start rows) :
    source.InternalGraphElementary (h.inputBound D.toFiniteTraceRows.toInternalTraceRows.actions)
      (h.word D.toFiniteTraceRows.toInternalTraceRows.actions).bound (D.traceGraph h) :=
  h.internalCompositeGraph_elementary D.toFiniteTraceRows.toInternalTraceRows (D.graphs_on_trace h)

variable (target : ModelStage.{u}) (j : source.model.ElementaryMap target.model)

theorem imageTraceGraph_elementary {paired start : Nat} {rows : List Nat} (h : FactorTrace a paired start rows) :
    target.InternalGraphElementary (h.inputBound (D.image target j).toFiniteTraceRows.toInternalTraceRows.actions)
      (h.word (D.image target j).toFiniteTraceRows.toInternalTraceRows.actions).bound (j (D.traceGraph h)) := by
  rw [D.traceSource_image target j, D.traceBound_image target j]
  exact (source.internalGraphElementary_image target j _ _ _).mpr (D.traceGraph_elementary h)

/-- Exact equality of the entire historical composite graph. This proof
uses first-order composition, so it covers every input of the image domain. -/
theorem traceGraph_image {paired start : Nat} {rows : List Nat} (h : FactorTrace a paired start rows) :
    (D.image target j).traceGraph h = j (D.traceGraph h) := by
  induction h with
  | @single r hp hn =>
    let index : FiniteRowIndex a := ⟨r, predecessor_row_index hp⟩
    have old := FactorTrace.internalCompositeGraph_single D.toFiniteTraceRows.toInternalTraceRows hp hn
      (D.graphs_on_trace (FactorTrace.single hp hn))
      (D.toFiniteTraceRows.represents_valid index (D.graph index) (D.graph_represents index))
    have new := FactorTrace.internalCompositeGraph_single (D.image target j).toFiniteTraceRows.toInternalTraceRows hp hn
      ((D.image target j).graphs_on_trace (FactorTrace.single hp hn))
      ((D.image target j).toFiniteTraceRows.represents_valid index _ ((D.image target j).graph_represents index))
    exact new.trans (congrArg j old).symm
  | @cons r next tail hp hn inner ih =>
    let index : FiniteRowIndex a := ⟨r, predecessor_row_index hp⟩
    let parent := FactorTrace.cons hp hn inner
    have old := FactorTrace.internalCompositeGraph_cons_spec D.toFiniteTraceRows.toInternalTraceRows hp hn inner
      (D.graphs_on_trace parent) (D.graphs_on_trace inner)
      (D.toFiniteTraceRows.represents_valid index (D.graph index) (D.graph_represents index))
    have new := FactorTrace.internalCompositeGraph_cons_spec (D.image target j).toFiniteTraceRows.toInternalTraceRows hp hn inner
      ((D.image target j).graphs_on_trace parent) ((D.image target j).graphs_on_trace inner)
      ((D.image target j).toFiniteTraceRows.represents_valid index _ ((D.image target j).graph_represents index))
    have imageSpec := (j.compositionSpec_iff _ _ _).mpr old
    change graphCompositionSpec ((D.image target j).traceGraph inner).val ((D.image target j).graph index).val
      ((D.image target j).traceGraph parent).val at new
    change graphCompositionSpec (j (D.traceGraph inner)).val (j (D.graph index)).val
      (j (D.traceGraph parent)).val at imageSpec
    apply Subtype.ext
    apply functionGraph_ext ((target.model.function_absolute _ _ _).mp ((D.image target j).traceGraph_elementary parent).1)
      ((target.model.function_absolute _ _ _).mp (D.imageTraceGraph_elementary target j parent).1)
    intro x y
    rw [new x y, imageSpec x y]
    change (∃ z, ZFSet.pair x z ∈ ((D.image target j).traceGraph inner).val ∧
      ZFSet.pair z y ∈ (j (D.graph index)).val) ↔ _
    rw [ih]

end IBLP.FiniteBoundedData
