import IBLP.Model.Schemas

namespace IBLP
open FullMarkedBLP
universe u

/-- 参数、原集合、输出集合，最后一个量词变量是被测试的元素。 -/
def separationMatrix {n : Nat} (phi : RankPredicateFormula 0 (n + 1)) : RankPredicateFormula 0 (n + 2) :=
  let left : RankPredicateFormula 0 (n + 3) := .member (Fin.last (n + 2)) (Fin.last (n + 1)).castSucc
  let right : RankPredicateFormula 0 (n + 3) :=
    (RankPredicateFormula.member (Fin.last (n + 2)) (Fin.last n).castSucc.castSucc).and
      (phi.relabelSets (Fin.lastCases (Fin.last (n + 2)) (fun i => i.castAdd 3)))
  .all ((left.imp right).and (right.imp left))

theorem separationMatrix_realize (M : TransitiveClass.{u}) {n : Nat}
    (phi : RankPredicateFormula 0 (n + 1)) (values : Fin n → M.Element) (x z : M.Element) :
    M.realize (separationMatrix phi) (Fin.snoc (Fin.snoc values x) z) ↔
      ∀ w : M.Element, w.val ∈ z.val ↔ w.val ∈ x.val ∧ M.realize phi (Fin.snoc values w) := by
  change (∀ w, M.realize _ (Fin.snoc (Fin.snoc (Fin.snoc values x) z) w)) ↔ _
  apply forall_congr'
  intro w
  simp only [M.realize_and, TransitiveClass.realize, M.realize_relabel]
  have compatible : Fin.snoc (Fin.snoc (Fin.snoc values x) z) w ∘
      Fin.lastCases (Fin.last (n + 2)) (fun i : Fin n => i.castAdd 3) = Fin.snoc values w := by
    funext i
    cases i using Fin.lastCases with
    | last => simp
    | cast i =>
      simp only [Function.comp_apply, Fin.lastCases_castSucc, Fin.snoc_castSucc, Fin.snoc_castAdd]
      exact Fin.snoc_castSucc (α := fun _ => M.Element) x values i
  rw [compatible]
  simp only [Fin.snoc_last, Fin.snoc_castSucc]
  exact iff_def.symm

/-- 完整的一阶分离模式；谓词的量词在 stage.model 中解释。 -/
theorem ModelStage.separation_exists (stage : ModelStage.{u}) {n : Nat}
    (phi : RankPredicateFormula 0 (n + 1)) (values : Fin n → stage.model.Element)
    (x : stage.model.Element) :
    ∃ z : stage.model.Element, ∀ w : stage.model.Element,
      w.val ∈ z.val ↔ w.val ∈ x.val ∧ stage.model.realize phi (Fin.snoc values w) := by
  have initial : ∀ args, ∃ z, universeClass.{u}.toTransitiveClass.realize
      (separationMatrix phi) (Fin.snoc args z) := by
    intro args
    let params := Fin.init args
    let source := args (Fin.last n)
    let z : universeClass.{u}.toTransitiveClass.Element :=
      ⟨ZFSet.sep (fun w => universeClass.toTransitiveClass.realize phi
        (Fin.snoc params ⟨w, Set.mem_univ _⟩)) source.val, Set.mem_univ _⟩
    refine ⟨z, ?_⟩
    have h := (separationMatrix_realize universeClass.toTransitiveClass phi params source z).mpr
      (by
        intro w
        simp only [z, ZFSet.mem_sep]
        have eta : (⟨w.val, Set.mem_univ _⟩ : universeClass.{u}.toTransitiveClass.Element) = w :=
          Subtype.ext rfl
        rw [eta])
    simpa only [params, source, Fin.snoc_init_self] using h
  obtain ⟨z, hz⟩ := stage.transfer_exists (separationMatrix phi) initial (Fin.snoc values x)
  exact ⟨z, (separationMatrix_realize _ _ _ _ _).mp hz⟩

noncomputable def ModelStage.separation (stage : ModelStage.{u}) {n : Nat}
    (phi : RankPredicateFormula 0 (n + 1)) (values : Fin n → stage.model.Element)
    (x : stage.model.Element) : stage.model.Element := (stage.separation_exists phi values x).choose

theorem ModelStage.mem_separation (stage : ModelStage.{u}) {n : Nat}
    (phi : RankPredicateFormula 0 (n + 1)) (values : Fin n → stage.model.Element)
    (x w : stage.model.Element) :
    w.val ∈ (stage.separation phi values x).val ↔
      w.val ∈ x.val ∧ stage.model.realize phi (Fin.snoc values w) :=
  (stage.separation_exists phi values x).choose_spec w

noncomputable def ModelStage.difference (stage : ModelStage.{u}) (x y : stage.model.Element) :
    stage.model.Element := stage.separation (.not (.member 1 0)) ![y] x

theorem ModelStage.mem_difference (stage : ModelStage.{u}) (x y w : stage.model.Element) :
    w.val ∈ (stage.difference x y).val ↔ w.val ∈ x.val ∧ w.val ∉ y.val := by
  rw [ModelStage.difference, stage.mem_separation]
  rfl

theorem ModelStage.difference_val (stage : ModelStage.{u}) (x y : stage.model.Element) :
    (stage.difference x y).val = ZFSet.sep (fun w => w ∉ y.val) x.val := by
  apply ZFSet.ext
  intro w
  rw [ZFSet.mem_sep]
  constructor
  · intro hw
    exact (stage.mem_difference x y (stage.model.member (stage.difference x y) w hw)).mp hw
  · intro hw
    exact (stage.mem_difference x y (stage.model.member x w hw.1)).mpr hw

end IBLP
