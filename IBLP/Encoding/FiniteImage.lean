import IBLP.Encoding.FiniteSyntax
import IBLP.Model.SuccessorImage
import FullMarkedBLP.RankCriticalLimit

namespace IBLP
open FullMarkedBLP FirstOrder Language
universe u

theorem TransitiveClass.emptyFormula_realize (M : TransitiveClass.{u}) (x : M.Element) :
    rankEmptyFormula.Realize ![x] ↔ x.val = ∅ := by
  have semantics : rankEmptyFormula.Realize ![x] ↔ ∀ z : M.Element, z.val ∉ x.val := by
    simp [rankEmptyFormula, Formula.Realize, BoundedFormula.realize_all,
      BoundedFormula.realize_not, M.memAt_realize, Fin.snoc]
  rw [semantics]
  constructor
  · intro h
    apply (ZFSet.eq_empty _).mpr
    intro z hz
    exact h (M.member x z hz) hz
  · intro h z
    rw [h]
    exact ZFSet.notMem_empty _

namespace ModelStage
variable (source target : ModelStage.{u}) (j : source.model.ElementaryMap target.model)

theorem ordinal_zero_image : j (source.ordinal 0) = target.ordinal 0 := by
  have h := j.map_formula rankEmptyFormula ![source.ordinal 0]
  have tuple : j ∘ ![source.ordinal 0] = ![j (source.ordinal 0)] := by
    funext i; fin_cases i; rfl
  rw [tuple, target.model.emptyFormula_realize, source.model.emptyFormula_realize] at h
  apply Subtype.ext
  change (j (source.ordinal 0)).val = (0 : Ordinal.{u}).toZFSet
  simpa only [Ordinal.toZFSet_zero] using h.mpr (by simp [ordinal])

theorem ordinalImage_nat (n : Nat) : source.ordinalImage j (n : Ordinal.{u}) = n := by
  induction n with
  | zero =>
    have fixed := source.ordinal_zero_image target j
    simpa only [ordinalImage, ordinal, Ordinal.rank_toZFSet] using
      congrArg (fun x : target.model.Element => x.val.rank) fixed
  | succ n ih =>
    rw [Nat.cast_succ, ← Order.succ_eq_add_one, source.ordinalImage_succ, ih, Order.succ_eq_add_one]

theorem ordinal_nat_image (n : Nat) :
    j (source.ordinal (n : Ordinal.{u})) = target.ordinal (n : Ordinal.{u}) := by
  apply Subtype.ext
  rw [source.ordinalImage_compat, source.ordinalImage_nat target j n]
  rfl

theorem insert_image (x y : source.model.Element) :
    j (source.insert x y) = target.insert (j x) (j y) := by
  have h := j.map_formula modelInsertFormula ![source.insert x y, x, y]
  have tuple : j ∘ ![source.insert x y, x, y] = ![j (source.insert x y), j x, j y] := by
    funext i; fin_cases i <;> rfl
  rw [tuple, target.model.insertFormula_realize, source.model.insertFormula_realize] at h
  apply Subtype.ext
  rw [target.insert_val]
  exact h.mpr (source.insert_val x y)

theorem orderedPair_image (x y : source.model.Element) :
    j (source.orderedPair x y) = target.orderedPair (j x) (j y) := by
  have h := j.map_formula rankOrderedPairFormula ![source.orderedPair x y, x, y]
  have tuple : j ∘ ![source.orderedPair x y, x, y] = ![j (source.orderedPair x y), j x, j y] := by
    funext i; fin_cases i <;> rfl
  rw [tuple, target.model.orderedPairFormula_realize, source.model.orderedPairFormula_realize,
    target.model.orderedPair_absolute, source.model.orderedPair_absolute] at h
  apply Subtype.ext
  rw [target.orderedPair_val]
  exact h.mpr (source.orderedPair_val x y)

theorem finiteSet_image (xs : List source.model.Element) :
    j (source.finiteSet xs) = target.finiteSet (xs.map j) := by
  induction xs with
  | nil => exact source.ordinal_zero_image target j
  | cons x xs ih =>
    rw [finiteSet, source.insert_image target j, ih, List.map_cons, finiteSet]

theorem finiteRange_image {n : Nat} (values : Fin n → source.model.Element) :
    j (source.finiteRange values) = target.finiteRange (j ∘ values) := by
  rw [finiteRange, source.finiteSet_image target j, List.map_ofFn]
  rfl

/-- Every entry of the actual finite function graph is transported, while
its standard finite ordinal indices remain fixed. -/
theorem finiteGraph_image {n : Nat} (values : Fin n → source.model.Element) :
    j (source.finiteGraph values) = target.finiteGraph (j ∘ values) := by
  rw [finiteGraph, source.finiteRange_image target j]
  change target.finiteRange (j ∘ _) = target.finiteRange _
  congr 1
  funext i
  change j (source.orderedPair _ _) = _
  rw [source.orderedPair_image target j, source.ordinal_nat_image target j]
  rfl

theorem listCode_image (xs : List source.model.Element) :
    j (source.listCode xs) = target.listCode (xs.map j) := by
  induction xs with
  | nil => exact source.ordinal_zero_image target j
  | cons x xs ih =>
    rw [listCode, source.orderedPair_image target j, ih, List.map_cons, listCode]

theorem natListCode_image (xs : List Nat) :
    j (source.natListCode xs) = target.natListCode xs := by
  rw [natListCode, source.listCode_image target j, List.map_map, natListCode]
  congr 1
  apply List.map_congr_left
  intro n _
  exact source.ordinal_nat_image target j n

theorem rowCode_image (row : Row) : j (source.rowCode row) = target.rowCode row := by
  simp only [rowCode, source.orderedPair_image target j, source.natListCode_image target j,
    source.ordinal_nat_image target j]

/-- Arbitrary actual elementary stage maps preserve the exact finite pattern
code, including row order, all columns, step lengths, and every mark. -/
theorem patternCode_image (a : Pattern) :
    j (source.patternCode a) = target.patternCode a := by
  rw [patternCode, source.listCode_image target j, List.map_map, patternCode]
  congr 1
  apply List.map_congr_left
  intro row _
  exact source.rowCode_image target j row

end ModelStage
end IBLP
