import IBLP.Model.GraphOperations
import IBLP.Model.SetSatisfactionFormulaAtoms
import IBLP.Model.PairCoordinate

namespace IBLP
open FullMarkedBLP
universe u

def graphCompositionSpec (inner outer result : ZFSet.{u}) : Prop :=
  ∀ x y, ZFSet.pair x y ∈ result ↔ ∃ z, ZFSet.pair x z ∈ inner ∧ ZFSet.pair z y ∈ outer

def graphCompositionFormula : RankPredicateFormula 0 3 :=
  .all (.all ((rankFormulaGraphApplies 2 3 4).iff
    (((rankFormulaGraphApplies 0 3 5).and (rankFormulaGraphApplies 1 5 4)).ex)))

theorem graphCompositionFormula_realize (M : TransitiveClass.{u}) (inner outer result : M.Element) :
    M.realize graphCompositionFormula ![inner, outer, result] ↔ graphCompositionSpec inner.val outer.val result.val := by
  have sem : M.realize graphCompositionFormula ![inner, outer, result] ↔
      ∀ x y : M.Element, ZFSet.pair x.val y.val ∈ result.val ↔
        ∃ z : M.Element, ZFSet.pair x.val z.val ∈ inner.val ∧ ZFSet.pair z.val y.val ∈ outer.val := by
    simp [graphCompositionFormula, M.pure_iff_realize, M.realize_ex, M.realize_and,
      M.setGraphAtom_realize, TransitiveClass.realize]
  rw [sem]
  constructor
  · intro h x y
    constructor
    · intro edge
      have members := M.pair_components (M.transitive edge result.property)
      obtain ⟨z, hx, hy⟩ := (h ⟨x, members.1⟩ ⟨y, members.2⟩).mp edge
      exact ⟨z.val, hx, hy⟩
    · rintro ⟨z, hx, hy⟩
      have xz := M.pair_components (M.transitive hx inner.property)
      have zy := M.pair_components (M.transitive hy outer.property)
      exact (h ⟨x, xz.1⟩ ⟨y, zy.2⟩).mpr ⟨⟨z, xz.2⟩, hx, hy⟩
  · intro h x y
    constructor
    · intro edge
      obtain ⟨z, hx, hy⟩ := (h x.val y.val).mp edge
      exact ⟨⟨z, (M.pair_components (M.transitive hx inner.property)).2⟩, hx, hy⟩
    · rintro ⟨z, hx, hy⟩
      exact (h x.val y.val).mpr ⟨z.val, hx, hy⟩

theorem TransitiveClass.ElementaryMap.compositionSpec_iff {M N : TransitiveClass.{u}}
    (j : M.ElementaryMap N) (inner outer result : M.Element) :
    graphCompositionSpec (j inner).val (j outer).val (j result).val ↔
      graphCompositionSpec inner.val outer.val result.val := by
  have h := j.realize_iff graphCompositionFormula ![inner, outer, result]
  have args : j ∘ ![inner, outer, result] = ![j inner, j outer, j result] := by
    funext i; fin_cases i <;> rfl
  simpa only [args, graphCompositionFormula_realize] using h

/-- Equality of all pair edges determines a function graph, with junk
excluded by the actual function predicates. -/
theorem functionGraph_ext {d r d' r' f g : ZFSet.{u}} (hf : ZFSet.IsFunc d r f)
    (hg : ZFSet.IsFunc d' r' g) (edges : ∀ x y, ZFSet.pair x y ∈ f ↔ ZFSet.pair x y ∈ g) : f = g := by
  apply ZFSet.ext
  intro p
  constructor
  · intro hp
    obtain ⟨x, _, y, _, rfl⟩ := ZFSet.mem_prod.mp (hf.1 hp)
    exact (edges x y).mp hp
  · intro hp
    obtain ⟨x, _, y, _, rfl⟩ := ZFSet.mem_prod.mp (hg.1 hp)
    exact (edges x y).mpr hp

end IBLP
