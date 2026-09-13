import IBLP.Model.Stage
import FullMarkedBLP.RankIntersectionPreservation

namespace IBLP
open FullMarkedBLP FirstOrder Language

universe u

theorem TransitiveClass.intersectionFormula_realize (M : TransitiveClass.{u}) (z x y : M.Element) :
    rankIntersectionFormula.Realize ![z, x, y] ↔ z.val = x.val ∩ y.val := by
  have semantics : rankIntersectionFormula.Realize ![z, x, y] ↔
      ∀ w : M.Element, w.val ∈ z.val ↔ w.val ∈ x.val ∧ w.val ∈ y.val := by
    simp [rankIntersectionFormula, Formula.Realize, BoundedFormula.realize_all,
      BoundedFormula.realize_iff, M.memAt_realize, Fin.snoc]
  rw [semantics]
  constructor
  · intro h
    apply ZFSet.ext
    intro w
    rw [ZFSet.mem_inter]
    constructor
    · intro hw
      exact (h (M.member z w hw)).mp hw
    · intro hw
      exact (h (M.member x w hw.1)).mpr hw
  · intro same w
    rw [same, ZFSet.mem_inter]

def intersectionSentence : RankPredicateFormula 0 0 :=
  .all (.all ((rankPredicateAtom rankIntersectionFormula ![2, 0, 1]).ex))

theorem intersectionSentence_realize (M : TransitiveClass.{u}) :
    M.realize intersectionSentence Fin.elim0 ↔
      ∀ x y : M.Element, ∃ z : M.Element, z.val = x.val ∩ y.val := by
  change (∀ x y, M.realize (rankPredicateAtom rankIntersectionFormula ![2, 0, 1]).ex
    (Fin.snoc (Fin.snoc Fin.elim0 x) y)) ↔ _
  apply forall_congr'
  intro x
  apply forall_congr'
  intro y
  rw [M.realize_ex]
  apply exists_congr
  intro z
  rw [M.realize_atom]
  have tuple : Fin.snoc (Fin.snoc (Fin.snoc Fin.elim0 x) y) z ∘ ![2, 0, 1] = ![z, x, y] := by
    funext i
    fin_cases i <;> rfl
  rw [tuple]
  exact M.intersectionFormula_realize z x y

/-- 交集存在性来自初始环境的真实集合构造及完整一阶输送。 -/
theorem ModelStage.intersection_exists (stage : ModelStage.{u}) (x y : stage.model.Element) :
    ∃ z : stage.model.Element, z.val = x.val ∩ y.val := by
  have initial : universeClass.{u}.toTransitiveClass.realize intersectionSentence Fin.elim0 := by
    apply (intersectionSentence_realize _).mpr
    intro x y
    exact ⟨⟨x.val ∩ y.val, Set.mem_univ _⟩, rfl⟩
  exact (intersectionSentence_realize _).mp (stage.transfer_closed _ initial) x y

noncomputable def ModelStage.intersection (stage : ModelStage.{u}) (x y : stage.model.Element) :
    stage.model.Element := (stage.intersection_exists x y).choose

theorem ModelStage.intersection_val (stage : ModelStage.{u}) (x y : stage.model.Element) :
    (stage.intersection x y).val = x.val ∩ y.val := (stage.intersection_exists x y).choose_spec

end IBLP
