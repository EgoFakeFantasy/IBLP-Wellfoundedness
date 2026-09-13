import IBLP.Model.UniformGraphOperations
import IBLP.Realization.TraceGraphImage

namespace IBLP
open FullMarkedBLP
universe u

/-- A finite list of actual graph factors, composed from its last factor
outwards. The function condition rules out extraneous non-pair elements. -/
def GraphWord (stage : ModelStage.{u}) (graphs : Nat → stage.model.Element) :
    List Nat → stage.model.Element → Prop
  | [], _ => False
  | r :: rest, result => if rest = [] then result = graphs r else
      ∃ inner, GraphWord stage graphs rest inner ∧
        graphCompositionSpec inner.val (graphs r).val result.val ∧
        ∃ domain range, stage.model.IsFunction result domain range

theorem UniformDefinable.graph_word (rows : List Nat) {n : Nat}
    (graphs : Nat → Fin n) (result : Fin n) :
    UniformDefinable (fun (stage : ModelStage.{u}) v => GraphWord stage (v ∘ graphs) rows (v result)) := by
  induction rows generalizing n with
  | nil => exact falsity
  | cons r rest ih =>
    by_cases empty : rest = []
    · exact (equal result (graphs r)).congr (fun _ _ => by simp [GraphWord, empty])
    · have body := (ih (fun r => (graphs r).castSucc) (Fin.last n)).and
        ((graph_composition.relabel ![Fin.last n, (graphs r).castSucc, result.castSucc]).and
          (some_function.relabel ![result.castSucc]))
      exact body.exists_last.congr (fun stage v => by
        simp only [Function.comp_def, Fin.snoc_castSucc, Fin.snoc_last,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
        rw [GraphWord, if_neg empty]
        simp only [Matrix.cons_val_succ, Matrix.cons_val_zero, Fin.snoc_castSucc])

namespace FiniteBoundedData
variable {stage : ModelStage.{u}} {a : Pattern} (D : FiniteBoundedData stage a)

/-- The finite composition formula specifies precisely the graph already
constructed by the semantic trace, including all of its set elements. -/
theorem graphWord_iff {target start : Nat} {rows : List Nat} (h : FactorTrace a target start rows)
    (graphs : Nat → stage.model.Element) (saved : ∀ r : FiniteRowIndex a, graphs r.val = D.graph r)
    (result : stage.model.Element) : GraphWord stage graphs rows result ↔ result = D.traceGraph h := by
  induction h generalizing result with
  | @single r hp hn =>
    let index : FiniteRowIndex a := ⟨r, predecessor_row_index hp⟩
    have canonical := FactorTrace.internalCompositeGraph_single D.toFiniteTraceRows.toInternalTraceRows hp hn
      (D.graphs_on_trace (FactorTrace.single hp hn))
      (D.toFiniteTraceRows.represents_valid index (D.graph index) (D.graph_represents index))
    change D.traceGraph (FactorTrace.single hp hn) = D.graph index at canonical
    change result = graphs r ↔ result = D.traceGraph (FactorTrace.single hp hn)
    rw [saved index, canonical]
  | @cons r next rest hp hn inner ih =>
    let index : FiniteRowIndex a := ⟨r, predecessor_row_index hp⟩
    let parent := FactorTrace.cons hp hn inner
    have canonical := FactorTrace.internalCompositeGraph_cons_spec D.toFiniteTraceRows.toInternalTraceRows hp hn inner
      (D.graphs_on_trace parent) (D.graphs_on_trace inner)
      (D.toFiniteTraceRows.represents_valid index (D.graph index) (D.graph_represents index))
    change graphCompositionSpec (D.traceGraph inner).val (D.graph index).val (D.traceGraph parent).val at canonical
    rw [GraphWord, if_neg inner.nonempty]
    constructor
    · rintro ⟨inside, word, composition, domain, range, function⟩
      rw [(ih inside).mp word, saved index] at composition
      apply Subtype.ext
      apply functionGraph_ext ((stage.model.function_absolute _ _ _).mp function)
        ((stage.model.function_absolute _ _ _).mp (D.traceGraph_elementary parent).1)
      intro x y
      rw [composition x y, canonical x y]
    · intro same
      subst result
      exact ⟨D.traceGraph inner, (ih _).mpr rfl, (saved index).symm ▸ canonical,
        _, _, (D.traceGraph_elementary parent).1⟩

end FiniteBoundedData
end IBLP
