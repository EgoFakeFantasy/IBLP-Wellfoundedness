import IBLP.Model.Schemas
import FullMarkedBLP.RankPowersetPreservation

namespace IBLP
open FullMarkedBLP FirstOrder Language
universe u

theorem TransitiveClass.subsetFormula_realize (M : TransitiveClass.{u}) (x y : M.Element) :
    rankSubsetFormula.Realize ![x, y] ↔ x.val ⊆ y.val := by
  have semantics : rankSubsetFormula.Realize ![x, y] ↔
      ∀ z : M.Element, z.val ∈ x.val → z.val ∈ y.val := by
    simp [rankSubsetFormula, Formula.Realize, BoundedFormula.realize_all,
      BoundedFormula.realize_imp, M.memAt_realize, Fin.snoc]
  rw [semantics]
  constructor
  · exact fun h z hz => h (M.member x z hz) hz
  · exact fun h z hz => h hz

/-- 幂集的正确相对语义，只对 M 中的子集量化。 -/
theorem TransitiveClass.powersetFormula_realize (M : TransitiveClass.{u}) (p x : M.Element) :
    rankPowersetFormula.Realize ![p, x] ↔
      ∀ z : M.Element, z.val ∈ p.val ↔ z.val ⊆ x.val := by
  have semantics : rankPowersetFormula.Realize ![p, x] ↔
      ∀ z : M.Element, z.val ∈ p.val ↔
        ∀ w : M.Element, w.val ∈ z.val → w.val ∈ x.val := by
    simp [rankPowersetFormula, Formula.Realize, BoundedFormula.realize_all,
      BoundedFormula.realize_iff, BoundedFormula.realize_imp, M.memAt_realize, Fin.snoc]
  rw [semantics]
  apply forall_congr'
  intro z
  apply iff_congr Iff.rfl
  constructor
  · exact fun h w hw => h (M.member z w hw) hw
  · exact fun h w hw => h hw

theorem ModelStage.powerset_exists (stage : ModelStage.{u}) (x : stage.model.Element) :
    ∃ p : stage.model.Element, ∀ z : stage.model.Element, z.val ∈ p.val ↔ z.val ⊆ x.val := by
  let phi : RankPredicateFormula 0 2 := rankPredicateAtom rankPowersetFormula ![1, 0]
  have semantic (M : TransitiveClass.{u}) (values : Fin 1 → M.Element) (p : M.Element) :
      M.realize phi (Fin.snoc values p) ↔
        ∀ z : M.Element, z.val ∈ p.val ↔ z.val ⊆ (values 0).val := by
    rw [show phi = rankPredicateAtom rankPowersetFormula ![1, 0] from rfl, M.realize_atom]
    have tuple : Fin.snoc values p ∘ ![1, 0] = ![p, values 0] := by
      funext i
      fin_cases i <;> rfl
    rw [tuple]
    exact M.powersetFormula_realize p (values 0)
  have initial : ∀ values, ∃ p, universeClass.{u}.toTransitiveClass.realize phi (Fin.snoc values p) := by
    intro values
    refine ⟨⟨ZFSet.powerset (values 0).val, Set.mem_univ _⟩, ?_⟩
    apply (semantic _ _ _).mpr
    exact fun _ => ZFSet.mem_powerset
  obtain ⟨p, hp⟩ := stage.transfer_exists phi initial ![x]
  exact ⟨p, (semantic _ _ _).mp hp⟩

noncomputable def ModelStage.powerset (stage : ModelStage.{u}) (x : stage.model.Element) :
    stage.model.Element := (stage.powerset_exists x).choose

theorem ModelStage.mem_powerset (stage : ModelStage.{u}) (x z : stage.model.Element) :
    z.val ∈ (stage.powerset x).val ↔ z.val ⊆ x.val := (stage.powerset_exists x).choose_spec z

/-- 与环境幂集的准确对应还必须包含 z 属于 M 这一项。 -/
theorem ModelStage.mem_powerset_external (stage : ModelStage.{u}) (x : stage.model.Element)
    (z : ZFSet.{u}) : z ∈ (stage.powerset x).val ↔ z ∈ stage.model.carrier ∧ z ⊆ x.val := by
  constructor
  · intro hz
    have hm := stage.model.transitive hz (stage.powerset x).property
    exact ⟨hm, (stage.mem_powerset x ⟨z, hm⟩).mp hz⟩
  · rintro ⟨hm, hz⟩
    exact (stage.mem_powerset x ⟨z, hm⟩).mpr hz

end IBLP
