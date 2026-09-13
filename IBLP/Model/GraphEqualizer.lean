import IBLP.Model.Preimage
import IBLP.Model.PairCoordinate

namespace IBLP
open FullMarkedBLP
universe u

def graphEqualizerRelation : RankPredicateFormula 0 3 :=
  ((rankPredicateAtom rankGraphAppliesFormula ![0, 2, 3]).and
    (rankPredicateAtom rankGraphAppliesFormula ![1, 2, 3])).ex

theorem graphEqualizerRelation_realize (M : TransitiveClass.{u}) (p q x : M.Element) :
    M.realize graphEqualizerRelation (Fin.snoc ![p, q] x) ↔
      ∃ y : M.Element, ZFSet.pair x.val y.val ∈ p.val ∧ ZFSet.pair x.val y.val ∈ q.val := by
  simp [graphEqualizerRelation, M.realize_ex, M.realize_and, M.graphFormulaAtom_realize]

def graphEqualizerMatrix : RankPredicateFormula 0 4 :=
  .all ((RankPredicateFormula.member 4 3).iff
    ((RankPredicateFormula.member 4 0).and (graphEqualizerRelation.relabelSets ![1, 2, 4])))

theorem TransitiveClass.equalizerMatrix_realize (M : TransitiveClass.{u})
    (domain p q equalizer : M.Element) :
    M.realize graphEqualizerMatrix ![domain, p, q, equalizer] ↔
      equalizer.val = ZFSet.sep
        (fun x => ∃ y, ZFSet.pair x y ∈ p.val ∧ ZFSet.pair x y ∈ q.val) domain.val := by
  have sem : M.realize graphEqualizerMatrix ![domain, p, q, equalizer] ↔
      ∀ x : M.Element, x.val ∈ equalizer.val ↔ x.val ∈ domain.val ∧
        ∃ y : M.Element, ZFSet.pair x.val y.val ∈ p.val ∧ ZFSet.pair x.val y.val ∈ q.val := by
    simp [graphEqualizerMatrix, RankPredicateFormula.iff, M.realize_and, M.realize_relabel,
      TransitiveClass.realize, graphEqualizerRelation, M.realize_ex, M.graphFormulaAtom_realize,
      iff_def, Fin.snoc, Function.comp_def]
  have inside {x y : ZFSet.{u}} (edge : ZFSet.pair x y ∈ p.val) : y ∈ M.carrier :=
    (M.pair_components (M.transitive edge p.property)).2
  rw [sem]
  constructor
  · intro h
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_sep]
    constructor
    · intro hx
      obtain ⟨hd, y, hp, hq⟩ := (h (M.member equalizer x hx)).mp hx
      exact ⟨hd, y.val, hp, hq⟩
    · rintro ⟨hd, y, hp, hq⟩
      exact (h (M.member domain x hd)).mpr ⟨hd, ⟨y, inside hp⟩, hp, hq⟩
  · intro h x
    rw [h, ZFSet.mem_sep]
    constructor
    · rintro ⟨hd, y, hp, hq⟩
      exact ⟨hd, ⟨y, inside hp⟩, hp, hq⟩
    · rintro ⟨hd, y, hp, hq⟩
      exact ⟨hd, y.val, hp, hq⟩

theorem TransitiveClass.ElementaryMap.equalizer_iff {M N : TransitiveClass.{u}}
    (j : M.ElementaryMap N) (domain p q equalizer : M.Element) :
    (j equalizer).val = ZFSet.sep
      (fun x => ∃ y, ZFSet.pair x y ∈ (j p).val ∧ ZFSet.pair x y ∈ (j q).val) (j domain).val ↔
      equalizer.val = ZFSet.sep
        (fun x => ∃ y, ZFSet.pair x y ∈ p.val ∧ ZFSet.pair x y ∈ q.val) domain.val := by
  have h := j.realize_iff graphEqualizerMatrix ![domain, p, q, equalizer]
  have args : j ∘ ![domain, p, q, equalizer] = ![j domain, j p, j q, j equalizer] := by
    funext i; fin_cases i <;> rfl
  rwa [args, M.equalizerMatrix_realize, N.equalizerMatrix_realize] at h

namespace ModelStage

noncomputable def graphEqualizer (stage : ModelStage.{u}) (domain p q : stage.model.Element) :
    stage.model.Element := stage.separation graphEqualizerRelation ![p, q] domain

theorem graphEqualizer_val (stage : ModelStage.{u}) (domain p q : stage.model.Element) :
    (stage.graphEqualizer domain p q).val = ZFSet.sep
      (fun x => ∃ y, ZFSet.pair x y ∈ p.val ∧ ZFSet.pair x y ∈ q.val) domain.val := by
  have sem (x : stage.model.Element) : x.val ∈ (stage.graphEqualizer domain p q).val ↔
      x.val ∈ domain.val ∧ ∃ y : stage.model.Element,
        ZFSet.pair x.val y.val ∈ p.val ∧ ZFSet.pair x.val y.val ∈ q.val := by
    rw [graphEqualizer, stage.mem_separation, graphEqualizerRelation_realize]
  apply ZFSet.ext
  intro x
  rw [ZFSet.mem_sep]
  constructor
  · intro hx
    obtain ⟨hd, y, hp, hq⟩ := (sem (stage.model.member _ x hx)).mp hx
    exact ⟨hd, y.val, hp, hq⟩
  · rintro ⟨hd, y, hp, hq⟩
    exact (sem (stage.model.member domain x hd)).mpr
      ⟨hd, ⟨y, (stage.model.pair_components (stage.model.transitive hp p.property)).2⟩, hp, hq⟩

end ModelStage
end IBLP
