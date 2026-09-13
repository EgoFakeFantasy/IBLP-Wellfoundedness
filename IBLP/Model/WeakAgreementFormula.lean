import IBLP.Model.InternalWeakTruncation
import IBLP.Realization.BoundedMapGraph

namespace IBLP
open FullMarkedBLP FirstOrder Language
universe u

theorem TransitiveClass.intersectionFormulaAtom_realize (M : TransitiveClass.{u}) {n : Nat}
    (z x y : Fin n) (values : Fin n → M.Element) :
    M.realize (rankPredicateAtom rankIntersectionFormula ![z, x, y]) values ↔
      (values z).val = (values x).val ∩ (values y).val := by
  rw [M.realize_atom]
  have tuple : values ∘ ![z, x, y] = ![values z, values x, values y] := by
    funext i; fin_cases i <;> rfl
  rw [tuple, M.intersectionFormula_realize]

/-- Parameters are a graph, its source cut, the input and the tested member.
The two witnesses are the truncated input and its actual graph value. -/
def graphWeakMembership : RankPredicateFormula 0 4 :=
  ((rankPredicateAtom rankIntersectionFormula ![4, 2, 1]).and
    ((rankPredicateAtom rankGraphAppliesFormula ![0, 4, 5]).and (.member 3 5))).ex.ex

theorem graphWeakMembership_realize (M : TransitiveClass.{u})
    (graph source z x : M.Element) :
    M.realize graphWeakMembership ![graph, source, z, x] ↔
      ∃ t y : M.Element, t.val = z.val ∩ source.val ∧
        ZFSet.pair t.val y.val ∈ graph.val ∧ x.val ∈ y.val := by
  simp [graphWeakMembership, M.realize_ex, M.realize_and,
    M.intersectionFormulaAtom_realize, M.graphFormulaAtom_realize, TransitiveClass.realize]

namespace TransitiveClass

def GraphWeakAgreement (M : TransitiveClass.{u})
    (f g sourceF sourceG cutoff : M.Element) : Prop :=
  ∀ x z : M.Element, x.val ∈ cutoff.val → z.val ∈ cutoff.val →
    ((∃ t y : M.Element, t.val = z.val ∩ sourceF.val ∧
        ZFSet.pair t.val y.val ∈ f.val ∧ x.val ∈ y.val) ↔
      (∃ t y : M.Element, t.val = z.val ∩ sourceG.val ∧
        ZFSet.pair t.val y.val ∈ g.val ∧ x.val ∈ y.val))

end TransitiveClass

/-- Exactly five set parameters; every quantifier is in the current model. -/
def modelWeakAgreement : RankPredicateFormula 0 5 :=
  let left : RankPredicateFormula 0 7 := graphWeakMembership.relabelSets ![0, 2, 6, 5]
  let right : RankPredicateFormula 0 7 := graphWeakMembership.relabelSets ![1, 3, 6, 5]
  .all (.all (((RankPredicateFormula.member 5 4).and (.member 6 4)).imp
    ((left.imp right).and (right.imp left))))

def modelWeakAgreementFormula : membershipLanguage.Formula (Fin 5) :=
  rankPredicateToFormula modelWeakAgreement

theorem modelWeakAgreement_realize (M : TransitiveClass.{u})
    (f g sourceF sourceG cutoff : M.Element) :
    M.realize modelWeakAgreement ![f, g, sourceF, sourceG, cutoff] ↔
      M.GraphWeakAgreement f g sourceF sourceG cutoff := by
  change (∀ x z, M.realize _ (Fin.snoc (Fin.snoc ![f, g, sourceF, sourceG, cutoff] x) z)) ↔ _
  simp only [M.realize_and, TransitiveClass.realize,
    M.realize_relabel]
  have leftTuple (x z : M.Element) :
      Fin.snoc (Fin.snoc ![f, g, sourceF, sourceG, cutoff] x) z ∘ ![(0 : Fin 7), 2, 6, 5] =
        ![f, sourceF, z, x] := by funext i; fin_cases i <;> rfl
  have rightTuple (x z : M.Element) :
      Fin.snoc (Fin.snoc ![f, g, sourceF, sourceG, cutoff] x) z ∘ ![(1 : Fin 7), 3, 6, 5] =
        ![g, sourceG, z, x] := by funext i; fin_cases i <;> rfl
  simp only [leftTuple, rightTuple, graphWeakMembership_realize]
  simp [TransitiveClass.GraphWeakAgreement, iff_def, and_imp]

theorem modelWeakAgreementFormula_realize (M : TransitiveClass.{u})
    (f g sourceF sourceG cutoff : M.Element) :
    modelWeakAgreementFormula.Realize ![f, g, sourceF, sourceG, cutoff] ↔
      M.GraphWeakAgreement f g sourceF sourceG cutoff := by
  rw [modelWeakAgreementFormula, ← M.realize_toFormula, modelWeakAgreement_realize]

theorem TransitiveClass.ElementaryMap.graphWeakAgreement_iff {M N : TransitiveClass.{u}}
    (j : M.ElementaryMap N) (f g sourceF sourceG cutoff : M.Element) :
    N.GraphWeakAgreement (j f) (j g) (j sourceF) (j sourceG) (j cutoff) ↔
      M.GraphWeakAgreement f g sourceF sourceG cutoff := by
  have h := j.realize_iff modelWeakAgreement ![f, g, sourceF, sourceG, cutoff]
  have tuple : j ∘ ![f, g, sourceF, sourceG, cutoff] =
      ![j f, j g, j sourceF, j sourceG, j cutoff] := by funext i; fin_cases i <;> rfl
  simpa only [tuple, modelWeakAgreement_realize] using h

namespace ModelStage

theorem rankCut_internal_val (stage : ModelStage.{u}) (alpha : Ordinal.{u})
    (z : stage.model.Element) :
    (stage.rankCut alpha z).val = z.val ∩ (stage.hierarchy alpha).val := by
  rw [stage.rankCut_val, ← stage.cut_val, ModelStage.cut, stage.intersection_val]

theorem graphWeakMembership_iff (stage : ModelStage.{u})
    {alpha beta : Ordinal.{u}} {graph : stage.model.Element} {k : stage.BoundedMap alpha beta}
    (represents : stage.RepresentsBoundedMap graph k) (z x : stage.model.Element) :
    stage.model.realize graphWeakMembership ![graph, stage.hierarchy alpha, z, x] ↔
      x.val ∈ (stage.weakAction k z).val := by
  rw [graphWeakMembership_realize]
  constructor
  · rintro ⟨t, y, ht, edge, member⟩
    have same : t.val = (stage.rankCut alpha z).val := ht.trans (stage.rankCut_internal_val alpha z).symm
    rw [same] at edge
    have unique := (represents.1.2 (stage.rankCut alpha z).val
      ((stage.mem_hierarchy _ _).mpr (stage.rankCut alpha z).property)).unique
      edge (represents.2 (stage.rankCut alpha z))
    simpa only [unique] using member
  · intro member
    exact ⟨stage.rankInclude _ (stage.rankCut alpha z), stage.weakAction k z,
      stage.rankCut_internal_val alpha z, represents.2 (stage.rankCut alpha z), member⟩

/-- There is no comparison requirement between the agreement cutoff and
either source. The source truncations are part of the finite formula. -/
theorem graphWeakAgreement_iff (stage : ModelStage.{u})
    {alpha beta gamma eta : Ordinal.{u}} {f g : stage.model.Element}
    {k : stage.BoundedMap alpha beta} {l : stage.BoundedMap gamma eta}
    (hf : stage.RepresentsBoundedMap f k) (hg : stage.RepresentsBoundedMap g l)
    (ha : Order.IsSuccLimit alpha) (hc : Order.IsSuccLimit gamma) (delta : Ordinal.{u}) :
    stage.model.GraphWeakAgreement f g (stage.hierarchy alpha) (stage.hierarchy gamma)
      (stage.hierarchy delta) ↔
      CutAction.WeakAgreement (stage.boundedCutAction ha k) (stage.boundedCutAction hc l) delta := by
  unfold TransitiveClass.GraphWeakAgreement CutAction.WeakAgreement
  simp only [← graphWeakMembership_realize, stage.graphWeakMembership_iff hf,
    stage.graphWeakMembership_iff hg, stage.mem_hierarchy_iff]
  rfl

theorem graphWeakAgreement_iff_allInputs (stage : ModelStage.{u})
    {alpha beta gamma eta : Ordinal.{u}} {f g : stage.model.Element}
    {k : stage.BoundedMap alpha beta} {l : stage.BoundedMap gamma eta}
    (hf : stage.RepresentsBoundedMap f k) (hg : stage.RepresentsBoundedMap g l)
    (ha : Order.IsSuccLimit alpha) (hc : Order.IsSuccLimit gamma)
    {delta : Ordinal.{u}} (hd : Order.IsSuccLimit delta) :
    stage.model.GraphWeakAgreement f g (stage.hierarchy alpha) (stage.hierarchy gamma)
      (stage.hierarchy delta) ↔
      CutAction.AllInputAgreement (stage.boundedCutAction ha k) (stage.boundedCutAction hc l) delta :=
  (stage.graphWeakAgreement_iff hf hg ha hc delta).trans (CutAction.weakAgreement_iff_allInputs hd)

end ModelStage
end IBLP
