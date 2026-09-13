import IBLP.Realization.TraceGraphImage

namespace IBLP.FiniteBoundedData
open FullMarkedBLP
universe u
variable {M N : ModelStage.{u}} {a b : IBLP.Pattern}
  (D : FiniteBoundedData M a) (E : FiniteBoundedData N b)

def RowGraphValuesEqual (r s : Nat) : Prop :=
  ∀ (hr : 0 < r ∧ r ≤ a.length) (hs : 0 < s ∧ s ≤ b.length),
    (D.graph ⟨r, hr⟩).val = (E.graph ⟨s, hs⟩).val

/-- Composite graph equality is absolute when all of its actual factors
are the same sets, even across different model stages and row labels. -/
theorem traceGraph_congr_values {target start target' start' : Nat} {rows rows' : List Nat}
    (h : FactorTrace a target start rows) (h' : FactorTrace b target' start' rows')
    (matched : List.Forall₂ (D.RowGraphValuesEqual E) rows rows') :
    (D.traceGraph h).val = (E.traceGraph h').val := by
  induction h generalizing target' start' rows' with
  | @single r hp hn =>
    cases h' with
    | @single s hp' hn' =>
      cases matched with
      | cons same rest =>
        let ri : FiniteRowIndex a := ⟨r, predecessor_row_index hp⟩
        let si : FiniteRowIndex b := ⟨_, predecessor_row_index hp'⟩
        have left := FactorTrace.internalCompositeGraph_single D.toFiniteTraceRows.toInternalTraceRows hp hn
          (D.graphs_on_trace (FactorTrace.single hp hn))
          (D.toFiniteTraceRows.represents_valid ri (D.graph ri) (D.graph_represents ri))
        have right := FactorTrace.internalCompositeGraph_single E.toFiniteTraceRows.toInternalTraceRows hp' hn'
          (E.graphs_on_trace (FactorTrace.single hp' hn'))
          (E.toFiniteTraceRows.represents_valid si (E.graph si) (E.graph_represents si))
        exact (congrArg Subtype.val left).trans
          ((same ri.property si.property).trans (congrArg Subtype.val right).symm)
    | @cons s next rows hp' hn' inner' =>
      cases matched with
      | cons same rest =>
        cases rest
        exact False.elim (inner'.nonempty rfl)
  | @cons r next rows hp hn inner ih =>
    cases h' with
    | @single s hp' hn' =>
      cases matched with
      | cons same rest =>
        have empty : rows = [] := by simpa using rest.length_eq
        exact False.elim (inner.nonempty empty)
    | @cons s next' rows' hp' hn' inner' =>
      cases matched with
      | cons same rest =>
        let ri : FiniteRowIndex a := ⟨r, predecessor_row_index hp⟩
        let si : FiniteRowIndex b := ⟨_, predecessor_row_index hp'⟩
        let parent := FactorTrace.cons hp hn inner
        let parent' := FactorTrace.cons hp' hn' inner'
        have left := FactorTrace.internalCompositeGraph_cons_spec D.toFiniteTraceRows.toInternalTraceRows hp hn inner
          (D.graphs_on_trace parent) (D.graphs_on_trace inner)
          (D.toFiniteTraceRows.represents_valid ri (D.graph ri) (D.graph_represents ri))
        have right := FactorTrace.internalCompositeGraph_cons_spec E.toFiniteTraceRows.toInternalTraceRows hp' hn' inner'
          (E.graphs_on_trace parent') (E.graphs_on_trace inner')
          (E.toFiniteTraceRows.represents_valid si (E.graph si) (E.graph_represents si))
        change graphCompositionSpec (D.traceGraph inner).val (D.graph ri).val (D.traceGraph parent).val at left
        change graphCompositionSpec (E.traceGraph inner').val (E.graph si).val (E.traceGraph parent').val at right
        apply functionGraph_ext ((M.model.function_absolute _ _ _).mp (D.traceGraph_elementary parent).1)
          ((N.model.function_absolute _ _ _).mp (E.traceGraph_elementary parent').1)
        intro x y
        rw [left x y, right x y, ih inner' rest, same ri.property si.property]

end IBLP.FiniteBoundedData
