import IBLP.Extender.Representative
import IBLP.Model.CountableImage

namespace IBLP.Extender
open FullMarkedBLP
universe u

/-- Graph sequence, omega, common input, complete output sequence graph. -/
def sequenceBundleMatrix : RankPredicateFormula 0 4 :=
  ((rankPredicateAtom rankFunctionFormula ![3, 1, 4]).ex).and
    (.all (.all ((rankFormulaGraphApplies 0 4 5).imp
      (.all ((rankFormulaGraphApplies 5 2 6).imp (rankFormulaGraphApplies 3 4 6))))))

theorem sequenceBundleMatrix_realize (M : TransitiveClass.{u}) (graphs omega x h : M.Element) :
    M.realize sequenceBundleMatrix ![graphs, omega, x, h] ↔
      (∃ range : M.Element, ZFSet.IsFunc omega.val range.val h.val) ∧
        ∀ n g : M.Element, ZFSet.pair n.val g.val ∈ graphs.val →
          ∀ y : M.Element, ZFSet.pair x.val y.val ∈ g.val → ZFSet.pair n.val y.val ∈ h.val := by
  rw [sequenceBundleMatrix, M.realize_and]
  apply and_congr
  · rw [M.realize_ex]
    apply exists_congr
    intro range
    rw [M.realize_atom]
    have args : Fin.snoc ![graphs, omega, x, h] range ∘ ![3, 1, 4] = ![h, omega, range] := by
      funext i; fin_cases i <;> rfl
    rw [args, M.functionFormula_realize, M.function_absolute]
  · simp [M.setGraphAtom_realize, TransitiveClass.realize]

namespace Representative
variable {stage : ModelStage.{u}} {alpha : Ordinal.{u}}

theorem sequence_exists (fs : Nat → Representative stage alpha) :
    ∃ h : Representative stage alpha, ∀ x : Derivation.Seed stage alpha,
      (∃ range : stage.model.Element, ZFSet.IsFunc Ordinal.omega0.toZFSet range.val (h.value x).val) ∧
      ∀ n : Nat, ZFSet.pair (n : Ordinal.{u}).toZFSet ((fs n).value x).val ∈ (h.value x).val := by
  classical
  let graphs := stage.countableGraph (fun n => (fs n).graph)
  let values : Fin 2 → stage.model.Element := ![graphs, stage.ordinal Ordinal.omega0]
  have total (x : stage.model.Element) (hx : x.val ∈ (stage.hierarchy alpha).val) :
      ∃ h : stage.model.Element, stage.model.realize sequenceBundleMatrix (Fin.snoc (Fin.snoc values x) h) := by
    let a : Derivation.Seed stage alpha := ⟨x.val, (stage.mem_hierarchy alpha x.val).mp hx⟩
    let h := stage.countableGraph (fun n => (fs n).value a)
    refine ⟨h, ?_⟩
    have args : Fin.snoc (Fin.snoc values x) h = ![graphs, stage.ordinal Ordinal.omega0, x, h] := by
      funext i; fin_cases i <;> rfl
    rw [args, sequenceBundleMatrix_realize]
    refine ⟨?_, ?_⟩
    · exact ⟨stage.countableRange (fun n => (fs n).value a), stage.countableGraph_function _⟩
    · intro n g hng y hxy
      obtain ⟨k, hk⟩ := ZFSet.mem_range.mp hng
      obtain ⟨indexEq, graphEq⟩ := ZFSet.pair_inj.mp hk
      have edge : ZFSet.pair a.val y.val ∈ (fs k).graph.val := by rw [graphEq]; exact hxy
      have valueEq := (fs k).value_unique a y edge
      apply ZFSet.mem_range.mpr
      refine ⟨k, ?_⟩
      change ZFSet.pair (k : Ordinal.{u}).toZFSet ((fs k).value a).val = ZFSet.pair n.val y.val
      rw [indexEq, ← valueEq]
  let choice := stage.choiceFunction sequenceBundleMatrix values (stage.hierarchy alpha) total
  let h : Representative stage alpha := ⟨choice.range, choice.graph, choice.isFunction⟩
  refine ⟨h, fun x => ?_⟩
  have sem := choice.satisfies (stage.rankInclude _ x) (h.value x) (h.value_edge x)
  have args : Fin.snoc (Fin.snoc values (stage.rankInclude _ x)) (h.value x) =
      ![graphs, stage.ordinal Ordinal.omega0, stage.rankInclude _ x, h.value x] := by
    funext i; fin_cases i <;> rfl
  rw [args, sequenceBundleMatrix_realize] at sem
  refine ⟨sem.1, fun n => ?_⟩
  apply sem.2 (stage.ordinal (n : Ordinal.{u})) (fs n).graph
  · exact ZFSet.mem_range.mpr ⟨n, rfl⟩
  · exact (fs n).value_edge x

end Representative
end IBLP.Extender
