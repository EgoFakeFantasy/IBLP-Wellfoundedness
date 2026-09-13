import IBLP.Model.SetSatisfactionFormulaAtoms

namespace IBLP
open FullMarkedBLP
universe u

theorem pair_components_mem {domain a b : ZFSet.{u}} (transitive : ZFSet.IsTransitive domain)
    (inside : ZFSet.pair a b ∈ domain) : a ∈ domain ∧ b ∈ domain := by
  have pairInside : ({a, b} : ZFSet.{u}) ∈ domain := transitive _ inside (by simp [ZFSet.pair])
  exact ⟨transitive _ pairInside (by simp), transitive _ pairInside (by simp)⟩

theorem TransitiveClass.pair_components {M : TransitiveClass.{u}} {a b : ZFSet.{u}}
    (inside : ZFSet.pair a b ∈ M.carrier) : a ∈ M.carrier ∧ b ∈ M.carrier := by
  have pairInside : ({a, b} : ZFSet.{u}) ∈ M.carrier := M.transitive (by simp [ZFSet.pair]) inside
  exact ⟨M.transitive (by simp) pairInside, M.transitive (by simp) pairInside⟩

/-- Total coordinate relation, with empty output on inputs that are not pairs. -/
def pairCoordinate (right : Bool) (x y : ZFSet.{u}) : Prop :=
  (∃ a b, x = ZFSet.pair a b ∧ y = if right then b else a) ∨
    (y = ∅ ∧ ¬∃ a b, x = ZFSet.pair a b)

def pairCoordinateFormula (right : Bool) : RankPredicateFormula 0 2 :=
  (((rankFormulaOrderedPair 0 2 3).and (.equal 1 (if right then 3 else 2))).ex.ex).or
    ((rankFormulaEmpty 1).and ((rankFormulaOrderedPair 0 2 3).ex.ex).not)

theorem pairCoordinateFormula_realize (M : TransitiveClass.{u}) (right : Bool) (x y : M.Element) :
    M.realize (pairCoordinateFormula right) ![x, y] ↔ pairCoordinate right x.val y.val := by
  have sem : M.realize (pairCoordinateFormula right) ![x, y] ↔
      (∃ a b : M.Element, x.val = ZFSet.pair a.val b.val ∧ y = if right then b else a) ∨
        (y.val = ∅ ∧ ¬∃ a b : M.Element, x.val = ZFSet.pair a.val b.val) := by
    cases right <;> simp [pairCoordinateFormula, M.pure_or_realize, M.realize_and,
      M.realize_ex, M.realize_not, M.setOrderedPairAtom_realize, M.setEmptyAtom_realize,
      TransitiveClass.realize]
  have pairExists : (∃ a b : M.Element, x.val = ZFSet.pair a.val b.val) ↔
      ∃ a b, x.val = ZFSet.pair a b := by
    constructor
    · rintro ⟨a, b, same⟩; exact ⟨a.val, b.val, same⟩
    · rintro ⟨a, b, same⟩
      have inside := M.pair_components (same ▸ x.property)
      exact ⟨⟨a, inside.1⟩, ⟨b, inside.2⟩, same⟩
  rw [sem, pairExists]
  apply or_congr_left
  constructor
  · rintro ⟨a, b, same, value⟩
    refine ⟨a.val, b.val, same, ?_⟩
    cases right <;> simpa using congrArg Subtype.val value
  · rintro ⟨a, b, same, value⟩
    have inside := M.pair_components (same ▸ x.property)
    refine ⟨⟨a, inside.1⟩, ⟨b, inside.2⟩, same, ?_⟩
    apply Subtype.ext
    cases right <;> simpa using value

theorem pairCoordinate_pair (right : Bool) (a b y : ZFSet.{u}) :
    pairCoordinate right (ZFSet.pair a b) y ↔ y = if right then b else a := by
  constructor
  · rintro (⟨c, d, same, value⟩ | ⟨_, impossible⟩)
    · obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.mp same
      exact value
    · exact False.elim (impossible ⟨a, b, rfl⟩)
  · exact fun h => Or.inl ⟨a, b, rfl, h⟩

theorem pairCoordinate_unique {right : Bool} {x y z : ZFSet.{u}}
    (hy : pairCoordinate right x y) (hz : pairCoordinate right x z) : y = z := by
  rcases hy with ⟨a, b, rfl, value⟩ | ⟨rfl, impossible⟩
  · exact value.trans ((pairCoordinate_pair right a b z).mp hz).symm
  · rcases hz with ⟨a, b, pair, _⟩ | ⟨rfl, _⟩
    · exact False.elim (impossible ⟨a, b, pair⟩)
    · rfl

end IBLP
