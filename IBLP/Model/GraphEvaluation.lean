import IBLP.Model.GraphOperations

namespace IBLP
open FullMarkedBLP FirstOrder Language
universe u

/-- Evaluate a finite formula at values of finitely many function graphs.
The free variables are the graphs followed by their common input. -/
noncomputable def graphEvaluationFormula {n : Nat} (phi : membershipLanguage.Formula (Fin n)) :
    membershipLanguage.Formula (Fin (n + 1)) :=
  ((Formula.iInf (fun i : Fin n => rankGraphAppliesFormula.relabel
    ![Sum.inl i.castSucc, Sum.inl (Fin.last n), Sum.inr i])) ⊓
      phi.relabel Sum.inr).iExs (Fin n)

theorem graphEvaluationFormula_realize (M : TransitiveClass.{u}) {n : Nat}
    (phi : membershipLanguage.Formula (Fin n)) (graphs : Fin n → M.Element) (x : M.Element) :
    (graphEvaluationFormula phi).Realize (Fin.snoc graphs x) ↔
      ∃ values : Fin n → M.Element,
        (∀ i, ZFSet.pair x.val (values i).val ∈ (graphs i).val) ∧ phi.Realize values := by
  simp only [graphEvaluationFormula, Formula.realize_iExs, Formula.realize_inf,
    Formula.realize_iInf, Formula.realize_relabel]
  apply exists_congr
  intro values
  have args (i : Fin n) : Sum.elim (Fin.snoc graphs x) values ∘
      ![Sum.inl i.castSucc, Sum.inl (Fin.last n), Sum.inr i] = ![graphs i, x, values i] := by
    funext j; fin_cases j <;> simp
  simp only [args, M.graphAppliesFormula_realize, M.graphApplies_absolute]
  rfl

noncomputable def graphEvaluation {n : Nat} (phi : RankPredicateFormula 0 n) : RankPredicateFormula 0 (n + 1) :=
  rankPredicateAtom (graphEvaluationFormula (rankPredicateToFormula phi)) id

theorem graphEvaluation_realize (M : TransitiveClass.{u}) {n : Nat}
    (phi : RankPredicateFormula 0 n) (graphs : Fin n → M.Element) (x : M.Element) :
    M.realize (graphEvaluation phi) (Fin.snoc graphs x) ↔
      ∃ values : Fin n → M.Element,
        (∀ i, ZFSet.pair x.val (values i).val ∈ (graphs i).val) ∧ M.realize phi values := by
  rw [graphEvaluation, M.realize_atom]
  simp only [Function.comp_id, graphEvaluationFormula_realize, ← M.realize_toFormula]

end IBLP
