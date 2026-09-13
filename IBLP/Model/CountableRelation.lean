import IBLP.Model.GraphRead

namespace IBLP.ModelStage
open FullMarkedBLP
universe u

theorem taggedSet_exists (stage : ModelStage.{u}) (index domain : stage.model.Element) :
    ∃ result : stage.model.Element, ∀ z : ZFSet.{u},
      z ∈ result.val ↔ ∃ y, y ∈ domain.val ∧ z = ZFSet.pair index.val y := by
  let phi : RankPredicateFormula 0 3 := rankPredicateAtom rankOrderedPairFormula ![2, 0, 1]
  have sem (x y : stage.model.Element) : stage.model.realize phi (Fin.snoc (Fin.snoc ![index] x) y) ↔
      y.val = ZFSet.pair index.val x.val := by
    rw [show phi = rankPredicateAtom rankOrderedPairFormula ![2, 0, 1] from rfl, stage.model.realize_atom]
    have args : Fin.snoc (Fin.snoc ![index] x) y ∘ ![2, 0, 1] = ![y, index, x] := by
      funext i; fin_cases i <;> rfl
    rw [args, stage.model.orderedPairFormula_realize, stage.model.orderedPair_absolute]
  have functional (x : stage.model.Element) (_ : x.val ∈ domain.val) :
      ∃! y : stage.model.Element, stage.model.realize phi (Fin.snoc (Fin.snoc ![index] x) y) :=
    ⟨stage.orderedPair index x, (sem _ _).mpr (stage.orderedPair_val _ _),
      fun y hy => Subtype.ext (((sem _ _).mp hy).trans (stage.orderedPair_val _ _).symm)⟩
  obtain ⟨result, spec⟩ := stage.replacement_exists phi ![index] domain functional
  refine ⟨result, fun z => ?_⟩
  constructor
  · intro hz
    obtain ⟨x, hx, h⟩ := (spec (stage.model.member result z hz)).mp hz
    exact ⟨x.val, hx, (sem _ _).mp h⟩
  · rintro ⟨y, hy, rfl⟩
    let ym := stage.model.member domain y hy
    have h := (spec (stage.orderedPair index ym)).mpr
      ⟨ym, hy, (sem _ _).mpr (stage.orderedPair_val _ _)⟩
    simpa only [stage.orderedPair_val] using h

noncomputable def taggedSet (stage : ModelStage.{u}) (index domain : stage.model.Element) : stage.model.Element :=
  (stage.taggedSet_exists index domain).choose

theorem mem_taggedSet (stage : ModelStage.{u}) (index domain : stage.model.Element) (z : ZFSet.{u}) :
    z ∈ (stage.taggedSet index domain).val ↔ ∃ y, y ∈ domain.val ∧ z = ZFSet.pair index.val y :=
  (stage.taggedSet_exists index domain).choose_spec z

theorem mem_countableUnion (stage : ModelStage.{u}) (f : Nat → stage.model.Element) (z : ZFSet.{u}) :
    z ∈ (stage.countableUnion f).val ↔ ∃ n, z ∈ (f n).val := by
  rw [countableUnion, stage.union_val, ZFSet.mem_sUnion]
  constructor
  · rintro ⟨y, hy, hz⟩
    obtain ⟨n, rfl⟩ := ZFSet.mem_range.mp hy
    exact ⟨n, hz⟩
  · rintro ⟨n, hn⟩
    exact ⟨(f n).val, ZFSet.mem_range.mpr ⟨n, rfl⟩, hn⟩

/-- A countable family is encoded as one actual relation of tagged members.
The family graph is used only through closure inside M, not as an input to K. -/
noncomputable def countableRelation (stage : ModelStage.{u}) (f : Nat → stage.model.Element) : stage.model.Element :=
  stage.countableUnion (fun n => stage.taggedSet (stage.ordinal (n : Ordinal.{u})) (f n))

theorem mem_countableRelation (stage : ModelStage.{u}) (f : Nat → stage.model.Element) (z : ZFSet.{u}) :
    z ∈ (stage.countableRelation f).val ↔
      ∃ n : Nat, ∃ y, y ∈ (f n).val ∧ z = ZFSet.pair (n : Ordinal.{u}).toZFSet y := by
  simp only [countableRelation, stage.mem_countableUnion, stage.mem_taggedSet, ordinal]

theorem countableRelation_edge_iff (stage : ModelStage.{u}) (f : Nat → stage.model.Element)
    (n : Nat) (x : ZFSet.{u}) :
    ZFSet.pair (n : Ordinal.{u}).toZFSet x ∈ (stage.countableRelation f).val ↔ x ∈ (f n).val := by
  rw [stage.mem_countableRelation]
  constructor
  · rintro ⟨m, y, hy, same⟩
    obtain ⟨indices, values⟩ := ZFSet.pair_inj.mp same
    have hm : n = m := Nat.cast_injective (Ordinal.toZFSet_injective indices)
    simpa only [← hm, ← values] using hy
  · intro hx
    exact ⟨n, x, hx, rfl⟩

end IBLP.ModelStage
