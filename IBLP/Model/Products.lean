import IBLP.Model.GraphEqualizer

namespace IBLP
open FullMarkedBLP
universe u

def productMatrix : RankPredicateFormula 0 3 :=
  .all ((RankPredicateFormula.member 3 2).iff
    (((RankPredicateFormula.member 4 0).and
      ((RankPredicateFormula.member 5 1).and (rankFormulaOrderedPair 3 4 5))).ex.ex))

theorem ModelStage.productMatrix_realize (stage : ModelStage.{u}) (left right product : stage.model.Element) :
    stage.model.realize productMatrix ![left, right, product] ↔ product.val = ZFSet.prod left.val right.val := by
  have sem : stage.model.realize productMatrix ![left, right, product] ↔
      ∀ p : stage.model.Element, p.val ∈ product.val ↔ ∃ x y : stage.model.Element,
        x.val ∈ left.val ∧ y.val ∈ right.val ∧ p.val = ZFSet.pair x.val y.val := by
    simp [productMatrix, stage.model.pure_iff_realize, stage.model.realize_ex,
      stage.model.realize_and, stage.model.setOrderedPairAtom_realize, TransitiveClass.realize]
  rw [sem]
  constructor
  · intro h
    apply ZFSet.ext
    intro p
    constructor
    · intro hp
      obtain ⟨x, y, hx, hy, same⟩ := (h (stage.model.member product p hp)).mp hp
      change p = ZFSet.pair x.val y.val at same
      rw [same]
      exact ZFSet.pair_mem_prod.mpr ⟨hx, hy⟩
    · intro hp
      obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.mp hp
      let x' := stage.model.member left x hx
      let y' := stage.model.member right y hy
      have hpair := (h (stage.orderedPair x' y')).mpr ⟨x', y', hx, hy, stage.orderedPair_val _ _⟩
      rwa [stage.orderedPair_val] at hpair
  · intro h p
    rw [h]
    constructor
    · intro hp
      obtain ⟨x, hx, y, hy, same⟩ := ZFSet.mem_prod.mp hp
      exact ⟨stage.model.member left x hx, stage.model.member right y hy, hx, hy, same⟩
    · rintro ⟨x, y, hx, hy, same⟩
      rw [same]
      exact ZFSet.pair_mem_prod.mpr ⟨hx, hy⟩

theorem ModelStage.product_exists (stage : ModelStage.{u}) (left right : stage.model.Element) :
    ∃ product : stage.model.Element, product.val = ZFSet.prod left.val right.val := by
  have initial : ∀ args, ∃ product, universeClass.{u}.toTransitiveClass.realize productMatrix (Fin.snoc args product) := by
    intro args
    let product : universeClass.{u}.toTransitiveClass.Element :=
      ⟨ZFSet.prod (args 0).val (args 1).val, Set.mem_univ _⟩
    refine ⟨product, ?_⟩
    have tuple : Fin.snoc args product = ![args 0, args 1, product] := by
      funext i; fin_cases i <;> rfl
    rw [tuple]
    exact (initialStage.productMatrix_realize (args 0) (args 1) product).mpr rfl
  obtain ⟨product, h⟩ := stage.transfer_exists productMatrix initial ![left, right]
  have tuple : Fin.snoc ![left, right] product = ![left, right, product] := by
    funext i; fin_cases i <;> rfl
  rw [tuple, stage.productMatrix_realize] at h
  exact ⟨product, h⟩

noncomputable def ModelStage.product (stage : ModelStage.{u}) (left right : stage.model.Element) :
    stage.model.Element := (stage.product_exists left right).choose

theorem ModelStage.product_val (stage : ModelStage.{u}) (left right : stage.model.Element) :
    (stage.product left right).val = ZFSet.prod left.val right.val := (stage.product_exists left right).choose_spec

end IBLP
