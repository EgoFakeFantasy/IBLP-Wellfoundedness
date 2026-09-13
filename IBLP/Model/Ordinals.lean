import IBLP.Model.Stage

namespace IBLP
open FullMarkedBLP FirstOrder Language
universe u

theorem TransitiveClass.ordinalFormula_realize (M : TransitiveClass.{u}) (x : M.Element) :
    rankOrdinalFormula.Realize ![x] ↔ ZFSet.IsOrdinal x.val := by
  have semantics : rankOrdinalFormula.Realize ![x] ↔
      (∀ y z : M.Element, y.val ∈ z.val → z.val ∈ x.val → y.val ∈ x.val) ∧
      (∀ y z w : M.Element, y.val ∈ z.val → z.val ∈ w.val → w.val ∈ x.val → y.val ∈ w.val) := by
    simp [rankOrdinalFormula, rankTransitiveFormula, rankMemTransitiveFormula, rankMemAtom,
      Formula.Realize, BoundedFormula.Realize, Relations.boundedFormula₂,
      Relations.boundedFormula, Structure.RelMap, Fin.snoc]
  rw [semantics]
  constructor
  · rintro ⟨ht, hm⟩
    constructor
    · intro y hy z hz
      exact ht (M.member (M.member x y hy) z hz) (M.member x y hy) hz hy
    · intro y z w hyz hzw hwx
      let w' := M.member x w hwx
      let z' := M.member w' z hzw
      exact hm (M.member z' y hyz) z' w' hyz hzw hwx
  · intro hx
    exact ⟨fun _ _ hyz hzx => hx.mem_trans hyz hzx,
      fun _ _ _ hyz hzw hwx => hx.mem_trans' hyz hzw hwx⟩

theorem TransitiveClass.ElementaryMap.mem_iff {M N : TransitiveClass.{u}} (j : M.ElementaryMap N)
    (x y : M.Element) : (j x).val ∈ (j y).val ↔ x.val ∈ y.val := by
  have h := j.map_rel (show membershipLanguage.Relations 2 from ⟨rfl⟩) ![x, y]
  simpa [Structure.RelMap, TransitiveClass.membershipStructure, Function.comp_def] using h

theorem TransitiveClass.ElementaryMap.isOrdinal_iff {M N : TransitiveClass.{u}}
    (j : M.ElementaryMap N) (x : M.Element) : ZFSet.IsOrdinal (j x).val ↔ ZFSet.IsOrdinal x.val := by
  have h := j.map_formula rankOrdinalFormula ![x]
  have tuple : j ∘ ![x] = ![j x] := by funext i; fin_cases i; rfl
  rw [tuple, N.ordinalFormula_realize, M.ordinalFormula_realize] at h
  exact h

noncomputable def ModelStage.ordinalAction (stage : ModelStage.{u}) (a : Ordinal.{u}) : Ordinal.{u} :=
  (stage.fromUniverse ⟨a.toZFSet, Set.mem_univ _⟩).val.rank

theorem ModelStage.ordinalAction_compat (stage : ModelStage.{u}) (a : Ordinal.{u}) :
    (stage.fromUniverse ⟨a.toZFSet, Set.mem_univ _⟩).val = (stage.ordinalAction a).toZFSet :=
  ((stage.fromUniverse.isOrdinal_iff _).mpr (ZFSet.isOrdinal_toZFSet a)).toZFSet_rank_eq.symm

theorem ModelStage.ordinalAction_strictMono (stage : ModelStage.{u}) : StrictMono stage.ordinalAction := by
  intro a b hab
  rw [← Ordinal.toZFSet_mem_toZFSet_iff, ← stage.ordinalAction_compat, ← stage.ordinalAction_compat]
  exact (stage.fromUniverse.mem_iff _ _).mpr (Ordinal.toZFSet_mem_toZFSet_iff.mpr hab)

theorem ModelStage.ordinalAction_le (stage : ModelStage.{u}) (a : Ordinal.{u}) :
    a ≤ stage.ordinalAction a := stage.ordinalAction_strictMono.le_apply

/-- 序数齐全由实际初等映射及传递性推出，不添加为阶段的假设。 -/
theorem ModelStage.ordinalComplete (stage : ModelStage.{u}) : stage.model.OrdinalComplete := by
  intro a
  have hlt : a < stage.ordinalAction (Order.succ a) := (Order.lt_succ a).trans_le (stage.ordinalAction_le _)
  have member := Ordinal.toZFSet_mem_toZFSet_iff.mpr hlt
  rw [← stage.ordinalAction_compat] at member
  exact stage.model.transitive member (stage.fromUniverse _).property

noncomputable def ModelStage.ordinal (stage : ModelStage.{u}) (a : Ordinal.{u}) : stage.model.Element :=
  ⟨a.toZFSet, stage.ordinalComplete a⟩

end IBLP
