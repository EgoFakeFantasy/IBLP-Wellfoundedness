import IBLP.Model.Separation
import IBLP.Model.Powerset

namespace IBLP
open FullMarkedBLP
universe u

def modelDifferenceMatrix : RankPredicateFormula 0 3 :=
  .all ((RankPredicateFormula.member 3 0).iff
    ((RankPredicateFormula.member 3 1).and (RankPredicateFormula.member 3 2).not))

theorem TransitiveClass.differenceMatrix_realize (M : TransitiveClass.{u}) (z x y : M.Element) :
    M.realize modelDifferenceMatrix ![z, x, y] ↔
      z.val = ZFSet.sep (fun w => w ∉ y.val) x.val := by
  have sem : M.realize modelDifferenceMatrix ![z, x, y] ↔
      ∀ w : M.Element, w.val ∈ z.val ↔ w.val ∈ x.val ∧ w.val ∉ y.val := by
    simp [modelDifferenceMatrix, RankPredicateFormula.iff, M.realize_and, M.realize_not,
      TransitiveClass.realize, iff_def]
  rw [sem]
  constructor
  · intro h
    apply ZFSet.ext
    intro w
    rw [ZFSet.mem_sep]
    constructor
    · exact fun hw => (h (M.member z w hw)).mp hw
    · exact fun hw => (h (M.member x w hw.1)).mpr hw
  · intro h w
    rw [h, ZFSet.mem_sep]

theorem TransitiveClass.ElementaryMap.subset_iff {M N : TransitiveClass.{u}}
    (j : M.ElementaryMap N) (x y : M.Element) :
    (j x).val ⊆ (j y).val ↔ x.val ⊆ y.val := by
  have h := j.map_formula rankSubsetFormula ![x, y]
  have args : j ∘ ![x, y] = ![j x, j y] := by funext i; fin_cases i <;> rfl
  rwa [args, M.subsetFormula_realize, N.subsetFormula_realize] at h

theorem TransitiveClass.ElementaryMap.difference_iff {M N : TransitiveClass.{u}}
    (j : M.ElementaryMap N) (z x y : M.Element) :
    (j z).val = ZFSet.sep (fun w => w ∉ (j y).val) (j x).val ↔
      z.val = ZFSet.sep (fun w => w ∉ y.val) x.val := by
  have h := j.realize_iff modelDifferenceMatrix ![z, x, y]
  have args : j ∘ ![z, x, y] = ![j z, j x, j y] := by funext i; fin_cases i <;> rfl
  rwa [args, M.differenceMatrix_realize, N.differenceMatrix_realize] at h

end IBLP
