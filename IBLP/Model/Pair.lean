import IBLP.Model.Schemas
import FullMarkedBLP.RankOrderedPairFormula

namespace IBLP
open FullMarkedBLP FirstOrder Language
universe u

namespace TransitiveClass

def IsUnorderedPair (M : TransitiveClass.{u}) (z x y : M.Element) : Prop :=
  ∀ w : M.Element, w.val ∈ z.val ↔ w = x ∨ w = y

theorem unorderedPair_absolute (M : TransitiveClass.{u}) (z x y : M.Element) :
    M.IsUnorderedPair z x y ↔ z.val = {x.val, y.val} := by
  constructor
  · intro h
    apply ZFSet.ext
    intro w
    constructor
    · intro hw
      rcases (h (M.member z w hw)).mp hw with he | he
      · exact ZFSet.mem_pair.mpr (Or.inl (congrArg Subtype.val he))
      · exact ZFSet.mem_pair.mpr (Or.inr (congrArg Subtype.val he))
    · intro hw
      rcases ZFSet.mem_pair.mp hw with he | he
      · subst w
        exact (h x).mpr (Or.inl rfl)
      · subst w
        exact (h y).mpr (Or.inr rfl)
  · intro hz w
    rw [hz, ZFSet.mem_pair]
    exact or_congr Subtype.val_inj Subtype.val_inj

theorem unorderedPairFormula_realize (M : TransitiveClass.{u}) (z x y : M.Element) :
    rankUnorderedPairFormula.Realize ![z, x, y] ↔ M.IsUnorderedPair z x y := by
  classical
  simp [rankUnorderedPairFormula, IsUnorderedPair, Formula.Realize, BoundedFormula.Realize,
    Relations.boundedFormula₂, Relations.boundedFormula, Structure.RelMap, Fin.snoc, imp_iff_not_or]

theorem unorderedPairAt_realize (M : TransitiveClass.{u}) {alpha : Type} {n : Nat}
    (z x y : alpha ⊕ Fin n) (free : alpha → M.Element) (bound : Fin n → M.Element) :
    (rankUnorderedPairAt z x y).Realize free bound ↔
      M.IsUnorderedPair (Sum.elim free bound z) (Sum.elim free bound x) (Sum.elim free bound y) := by
  classical
  simp [rankUnorderedPairAt, BoundedFormula.realize_relabel, rankUnorderedPairFormula,
    IsUnorderedPair, BoundedFormula.Realize, Function.comp_def,
    Relations.boundedFormula₂, Relations.boundedFormula, Structure.RelMap, Fin.snoc, imp_iff_not_or]

def IsOrderedPair (M : TransitiveClass.{u}) (z x y : M.Element) : Prop :=
  ∃ s t : M.Element, M.IsUnorderedPair s x x ∧ M.IsUnorderedPair t x y ∧ M.IsUnorderedPair z s t

theorem orderedPair_absolute (M : TransitiveClass.{u}) (z x y : M.Element) :
    M.IsOrderedPair z x y ↔ z.val = ZFSet.pair x.val y.val := by
  constructor
  · rintro ⟨s, t, hs, ht, hz⟩
    rw [M.unorderedPair_absolute] at hs ht hz
    rw [hz, hs, ht]
    simp [ZFSet.pair]
  · intro hz
    have hs : ({x.val, x.val} : ZFSet.{u}) ∈ z.val := by rw [hz]; simp [ZFSet.pair]
    have ht : ({x.val, y.val} : ZFSet.{u}) ∈ z.val := by rw [hz]; simp [ZFSet.pair]
    refine ⟨M.member z _ hs, M.member z _ ht, ?_, ?_, ?_⟩
    · exact (M.unorderedPair_absolute _ _ _).mpr rfl
    · exact (M.unorderedPair_absolute _ _ _).mpr rfl
    · apply (M.unorderedPair_absolute _ _ _).mpr
      simpa [ZFSet.pair, member] using hz

theorem orderedPairFormula_realize (M : TransitiveClass.{u}) (z x y : M.Element) :
    rankOrderedPairFormula.Realize ![z, x, y] ↔ M.IsOrderedPair z x y := by
  simp [rankOrderedPairFormula, Formula.Realize, BoundedFormula.realize_ex,
    BoundedFormula.realize_inf, M.unorderedPairAt_realize, IsOrderedPair, Fin.snoc]

end TransitiveClass

theorem ModelStage.unorderedPair_exists (stage : ModelStage.{u}) (x y : stage.model.Element) :
    ∃ z : stage.model.Element, z.val = {x.val, y.val} := by
  let phi : RankPredicateFormula 0 3 := rankPredicateAtom rankUnorderedPairFormula ![2, 0, 1]
  have semantic (M : TransitiveClass.{u}) (values : Fin 2 → M.Element) (z : M.Element) :
      M.realize phi (Fin.snoc values z) ↔ z.val = {(values 0).val, (values 1).val} := by
    rw [show phi = rankPredicateAtom rankUnorderedPairFormula ![2, 0, 1] from rfl, M.realize_atom]
    have tuple : Fin.snoc values z ∘ ![2, 0, 1] = ![z, values 0, values 1] := by
      funext i
      fin_cases i <;> rfl
    rw [tuple, M.unorderedPairFormula_realize, M.unorderedPair_absolute]
  have initial : ∀ values, ∃ z, universeClass.{u}.toTransitiveClass.realize phi (Fin.snoc values z) := by
    intro values
    exact ⟨⟨{(values 0).val, (values 1).val}, Set.mem_univ _⟩, (semantic _ _ _).mpr rfl⟩
  obtain ⟨z, hz⟩ := stage.transfer_exists phi initial ![x, y]
  exact ⟨z, (semantic _ _ _).mp hz⟩

noncomputable def ModelStage.unorderedPair (stage : ModelStage.{u}) (x y : stage.model.Element) :
    stage.model.Element := (stage.unorderedPair_exists x y).choose

theorem ModelStage.unorderedPair_val (stage : ModelStage.{u}) (x y : stage.model.Element) :
    (stage.unorderedPair x y).val = {x.val, y.val} := (stage.unorderedPair_exists x y).choose_spec

noncomputable def ModelStage.orderedPair (stage : ModelStage.{u}) (x y : stage.model.Element) :
    stage.model.Element := stage.unorderedPair (stage.unorderedPair x x) (stage.unorderedPair x y)

theorem ModelStage.orderedPair_val (stage : ModelStage.{u}) (x y : stage.model.Element) :
    (stage.orderedPair x y).val = ZFSet.pair x.val y.val := by
  simp [ModelStage.orderedPair, stage.unorderedPair_val, ZFSet.pair]

end IBLP
