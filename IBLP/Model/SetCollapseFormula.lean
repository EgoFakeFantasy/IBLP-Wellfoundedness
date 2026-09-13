import IBLP.Model.SetWellFounded
import FullMarkedBLP.FunctionGraphConstruction

namespace IBLP
open FullMarkedBLP
universe u

def collapseRecursionMatrix : RankPredicateFormula 0 3 :=
  .all (.all ((RankPredicateFormula.member 3 0).imp
    ((rankFormulaGraphApplies 2 3 4).imp
      (.all ((RankPredicateFormula.member 5 4).iff
        (((RankPredicateFormula.member 6 0).and
          ((rankFormulaGraphApplies 1 6 3).and (rankFormulaGraphApplies 2 6 5))).ex))))))

theorem collapseRecursionMatrix_realize (M : TransitiveClass.{u}) (domain relation graph : M.Element) :
    M.realize collapseRecursionMatrix ![domain, relation, graph] ↔
      ∀ x y : M.Element, x.val ∈ domain.val → ZFSet.pair x.val y.val ∈ graph.val →
        ∀ z : M.Element, z.val ∈ y.val ↔ ∃ p : M.Element, p.val ∈ domain.val ∧
          ZFSet.pair p.val x.val ∈ relation.val ∧ ZFSet.pair p.val z.val ∈ graph.val := by
  simp [collapseRecursionMatrix, M.pure_iff_realize, M.realize_ex,
    M.realize_and, M.setGraphAtom_realize, TransitiveClass.realize]

def collapseGraphMatrix : RankPredicateFormula 0 4 :=
  (rankPredicateAtom rankFunctionFormula ![3, 0, 2]).and
    (collapseRecursionMatrix.relabelSets ![0, 1, 3])

theorem collapseGraphMatrix_realize (M : TransitiveClass.{u}) (domain relation range graph : M.Element) :
    M.realize collapseGraphMatrix ![domain, relation, range, graph] ↔
      ZFSet.IsFunc domain.val range.val graph.val ∧
        M.realize collapseRecursionMatrix ![domain, relation, graph] := by
  rw [collapseGraphMatrix, M.realize_and]
  apply and_congr
  · rw [M.realize_atom]
    have args : ![domain, relation, range, graph] ∘ ![3, 0, 2] = ![graph, domain, range] := by
      funext i; fin_cases i <;> rfl
    rw [args, M.functionFormula_realize, M.function_absolute]
  · rw [M.realize_relabel]
    have args : ![domain, relation, range, graph] ∘ ![0, 1, 3] = ![domain, relation, graph] := by
      funext i; fin_cases i <;> rfl
    rw [args]

theorem universe_collapseGraph_exists (domain relation : universeClass.{u}.toTransitiveClass.Element)
    (wf : WellFounded (setRelation domain.val relation.val)) :
    ∃ range graph : universeClass.{u}.toTransitiveClass.Element,
      universeClass.toTransitiveClass.realize collapseGraphMatrix ![domain, relation, range, graph] := by
  classical
  letI : Small.{u} (SetDomain domain.val) := ZFSet.small_coe domain.val
  let c : SetDomain domain.val → ZFSet.{u} := Extender.collapse (setRelation domain.val relation.val) wf
  let range : universeClass.{u}.toTransitiveClass.Element := ⟨ZFSet.range c, Set.mem_univ _⟩
  let f : domain.val → range.val := fun x => ⟨c x, ZFSet.mem_range.mpr ⟨x, rfl⟩⟩
  let graph : universeClass.{u}.toTransitiveClass.Element := ⟨zfFunctionGraph f, Set.mem_univ _⟩
  refine ⟨range, graph, (collapseGraphMatrix_realize _ _ _ _ _).mpr ⟨zfFunctionGraph_isFunc f, ?_⟩⟩
  apply (collapseRecursionMatrix_realize _ _ _ _).mpr
  intro x y hx edge z
  obtain ⟨hx', valueEq⟩ := (mem_zfFunctionGraph f x.val y.val).mp edge
  change c ⟨x.val, hx'⟩ = y.val at valueEq
  rw [← valueEq, Extender.mem_collapse_iff]
  constructor
  · rintro ⟨p, hp, hz⟩
    refine ⟨⟨p.val, Set.mem_univ _⟩, p.property, hp, ?_⟩
    apply (mem_zfFunctionGraph f _ _).mpr
    exact ⟨p.property, hz⟩
  · rintro ⟨p, hp, hedge, hz⟩
    obtain ⟨hp', valueEq⟩ := (mem_zfFunctionGraph f _ _).mp hz
    exact ⟨⟨p.val, hp⟩, hedge, valueEq⟩

end IBLP
