import IBLP.Model.GraphEvaluation
import IBLP.Model.SetSatisfactionFormulaAtoms

namespace IBLP
open FullMarkedBLP FirstOrder Language
universe u

noncomputable def graphWitnessFormula {n : Nat} (phi : membershipLanguage.Formula (Fin (n + 1))) :
    membershipLanguage.Formula (Fin (n + 2)) :=
  ((Formula.iInf (fun i : Fin n => rankGraphAppliesFormula.relabel
    ![Sum.inl i.castSucc.castSucc, Sum.inl (Fin.last n).castSucc, Sum.inr i])) ⊓
      phi.relabel (Fin.lastCases (Sum.inl (Fin.last (n + 1))) Sum.inr)).iExs (Fin n)

theorem graphWitnessFormula_realize (M : TransitiveClass.{u}) {n : Nat}
    (phi : membershipLanguage.Formula (Fin (n + 1))) (graphs : Fin n → M.Element) (x y : M.Element) :
    (graphWitnessFormula phi).Realize (Fin.snoc (Fin.snoc graphs x) y) ↔
      ∃ values : Fin n → M.Element,
        (∀ i, ZFSet.pair x.val (values i).val ∈ (graphs i).val) ∧ phi.Realize (Fin.snoc values y) := by
  simp only [graphWitnessFormula, Formula.realize_iExs, Formula.realize_inf,
    Formula.realize_iInf, Formula.realize_relabel]
  apply exists_congr
  intro values
  have args (i : Fin n) : Sum.elim (Fin.snoc (Fin.snoc graphs x) y) values ∘
      ![Sum.inl i.castSucc.castSucc, Sum.inl (Fin.last n).castSucc, Sum.inr i] = ![graphs i, x, values i] := by
    funext j; fin_cases j <;> simp
  have body : Sum.elim (Fin.snoc (Fin.snoc graphs x) y) values ∘
      Fin.lastCases (Sum.inl (Fin.last (n + 1))) Sum.inr = Fin.snoc values y := by
    funext i
    cases i using Fin.lastCases with
    | last => simp
    | cast i => simp
  simp only [args, body, M.graphAppliesFormula_realize, M.graphApplies_absolute]

noncomputable def graphWitness {n : Nat} (phi : RankPredicateFormula 0 (n + 1)) :
    RankPredicateFormula 0 (n + 2) := rankPredicateAtom (graphWitnessFormula (rankPredicateToFormula phi)) id

theorem graphWitness_realize (M : TransitiveClass.{u}) {n : Nat}
    (phi : RankPredicateFormula 0 (n + 1)) (graphs : Fin n → M.Element) (x y : M.Element) :
    M.realize (graphWitness phi) (Fin.snoc (Fin.snoc graphs x) y) ↔
      ∃ values : Fin n → M.Element, (∀ i, ZFSet.pair x.val (values i).val ∈ (graphs i).val) ∧
        M.realize phi (Fin.snoc values y) := by
  rw [graphWitness, M.realize_atom]
  simp only [Function.comp_id, graphWitnessFormula_realize, ← M.realize_toFormula]

/-- Totalize witness selection only where no witness exists. The implication
is itself a finite formula, so internal Choice supplies an actual M-graph. -/
noncomputable def graphWitnessChoice {n : Nat} (phi : RankPredicateFormula 0 (n + 1)) :
    RankPredicateFormula 0 (n + 2) :=
  (((graphWitness phi).ex).relabelSets Fin.castSucc).imp (graphWitness phi)

theorem graphWitnessChoice_realize (M : TransitiveClass.{u}) {n : Nat}
    (phi : RankPredicateFormula 0 (n + 1)) (graphs : Fin n → M.Element) (x y : M.Element) :
    M.realize (graphWitnessChoice phi) (Fin.snoc (Fin.snoc graphs x) y) ↔
      ((∃ z : M.Element, M.realize (graphWitness phi) (Fin.snoc (Fin.snoc graphs x) z)) →
        M.realize (graphWitness phi) (Fin.snoc (Fin.snoc graphs x) y)) := by
  change (_ → _) ↔ _
  rw [M.realize_relabel]
  have args : Fin.snoc (Fin.snoc graphs x) y ∘ Fin.castSucc = Fin.snoc graphs x := by
    funext i; simp
  rw [args, M.realize_ex]

end IBLP
