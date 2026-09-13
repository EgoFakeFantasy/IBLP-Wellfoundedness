import IBLP.Model.GraphEqualizer

namespace IBLP
open FullMarkedBLP
universe u

def graphMembershipRelation : RankPredicateFormula 0 3 :=
  (((rankFormulaGraphApplies 0 2 3).and (rankFormulaGraphApplies 1 2 4)).and (.member 3 4)).ex.ex

theorem graphMembershipRelation_realize (M : TransitiveClass.{u}) (p q x : M.Element) :
    M.realize graphMembershipRelation (Fin.snoc ![p, q] x) ↔
      ∃ y z : M.Element, ZFSet.pair x.val y.val ∈ p.val ∧ ZFSet.pair x.val z.val ∈ q.val ∧ y.val ∈ z.val := by
  simp [graphMembershipRelation, M.realize_ex, M.realize_and, M.setGraphAtom_realize,
    TransitiveClass.realize, and_assoc]

def graphMembershipMatrix : RankPredicateFormula 0 4 :=
  .all ((RankPredicateFormula.member 4 3).iff
    ((RankPredicateFormula.member 4 0).and (graphMembershipRelation.relabelSets ![1, 2, 4])))

theorem TransitiveClass.membershipMatrix_realize (M : TransitiveClass.{u})
    (domain p q result : M.Element) :
    M.realize graphMembershipMatrix ![domain, p, q, result] ↔
      result.val = ZFSet.sep (fun x => ∃ y z, ZFSet.pair x y ∈ p.val ∧
        ZFSet.pair x z ∈ q.val ∧ y ∈ z) domain.val := by
  have sem : M.realize graphMembershipMatrix ![domain, p, q, result] ↔
      ∀ x : M.Element, x.val ∈ result.val ↔ x.val ∈ domain.val ∧
        ∃ y z : M.Element, ZFSet.pair x.val y.val ∈ p.val ∧
          ZFSet.pair x.val z.val ∈ q.val ∧ y.val ∈ z.val := by
    simp [graphMembershipMatrix, RankPredicateFormula.iff, M.realize_and, M.realize_relabel,
      TransitiveClass.realize, graphMembershipRelation, M.realize_ex, M.setGraphAtom_realize,
      iff_def, Fin.snoc, Function.comp_def, and_assoc]
  have inside {graph x y : ZFSet.{u}} (hg : graph ∈ M.carrier) (edge : ZFSet.pair x y ∈ graph) :
      y ∈ M.carrier := (M.pair_components (M.transitive edge hg)).2
  rw [sem]
  constructor
  · intro h
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_sep]
    constructor
    · intro hx
      obtain ⟨hd, y, z, hp, hq, hm⟩ := (h (M.member result x hx)).mp hx
      exact ⟨hd, y.val, z.val, hp, hq, hm⟩
    · rintro ⟨hd, y, z, hp, hq, hm⟩
      exact (h (M.member domain x hd)).mpr
        ⟨hd, ⟨y, inside p.property hp⟩, ⟨z, inside q.property hq⟩, hp, hq, hm⟩
  · intro h x
    rw [h, ZFSet.mem_sep]
    constructor
    · rintro ⟨hd, y, z, hp, hq, hm⟩
      exact ⟨hd, ⟨y, inside p.property hp⟩, ⟨z, inside q.property hq⟩, hp, hq, hm⟩
    · rintro ⟨hd, y, z, hp, hq, hm⟩
      exact ⟨hd, y.val, z.val, hp, hq, hm⟩

theorem TransitiveClass.ElementaryMap.membershipTest_iff {M N : TransitiveClass.{u}}
    (j : M.ElementaryMap N) (domain p q result : M.Element) :
    (j result).val = ZFSet.sep (fun x => ∃ y z, ZFSet.pair x y ∈ (j p).val ∧
      ZFSet.pair x z ∈ (j q).val ∧ y ∈ z) (j domain).val ↔
    result.val = ZFSet.sep (fun x => ∃ y z, ZFSet.pair x y ∈ p.val ∧
      ZFSet.pair x z ∈ q.val ∧ y ∈ z) domain.val := by
  have h := j.realize_iff graphMembershipMatrix ![domain, p, q, result]
  have args : j ∘ ![domain, p, q, result] = ![j domain, j p, j q, j result] := by
    funext i; fin_cases i <;> rfl
  rwa [args, M.membershipMatrix_realize, N.membershipMatrix_realize] at h

noncomputable def ModelStage.graphMembership (stage : ModelStage.{u}) (domain p q : stage.model.Element) :
    stage.model.Element := stage.separation graphMembershipRelation ![p, q] domain

theorem ModelStage.graphMembership_val (stage : ModelStage.{u}) (domain p q : stage.model.Element) :
    (stage.graphMembership domain p q).val = ZFSet.sep (fun x => ∃ y z,
      ZFSet.pair x y ∈ p.val ∧ ZFSet.pair x z ∈ q.val ∧ y ∈ z) domain.val := by
  have sem (x : stage.model.Element) : x.val ∈ (stage.graphMembership domain p q).val ↔
      x.val ∈ domain.val ∧ ∃ y z : stage.model.Element, ZFSet.pair x.val y.val ∈ p.val ∧
        ZFSet.pair x.val z.val ∈ q.val ∧ y.val ∈ z.val := by
    rw [ModelStage.graphMembership, stage.mem_separation, graphMembershipRelation_realize]
  apply ZFSet.ext
  intro x
  rw [ZFSet.mem_sep]
  constructor
  · intro hx
    obtain ⟨hd, y, z, hp, hq, hm⟩ := (sem (stage.model.member _ x hx)).mp hx
    exact ⟨hd, y.val, z.val, hp, hq, hm⟩
  · rintro ⟨hd, y, z, hp, hq, hm⟩
    exact (sem (stage.model.member domain x hd)).mpr ⟨hd,
      ⟨y, (stage.model.pair_components (stage.model.transitive hp p.property)).2⟩,
      ⟨z, (stage.model.pair_components (stage.model.transitive hq q.property)).2⟩, hp, hq, hm⟩

end IBLP
