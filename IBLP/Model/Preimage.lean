import IBLP.Model.GraphOperations

namespace IBLP
open FullMarkedBLP
universe u

/-- The two parameters are a graph and a target set. -/
def graphPreimageRelation : RankPredicateFormula 0 3 :=
  ((rankPredicateAtom rankGraphAppliesFormula ![0, 2, 3]).and (.member 3 1)).ex

theorem graphPreimageRelation_realize (M : TransitiveClass.{u}) (graph target x : M.Element) :
    M.realize graphPreimageRelation (Fin.snoc ![graph, target] x) ↔
      ∃ y : M.Element, ZFSet.pair x.val y.val ∈ graph.val ∧ y.val ∈ target.val := by
  simp [graphPreimageRelation, M.realize_ex, M.realize_and, M.graphFormulaAtom_realize,
    TransitiveClass.realize]

/-- Parameters are domain, graph, target, and preimage. -/
def graphPreimageMatrix : RankPredicateFormula 0 4 :=
  .all ((RankPredicateFormula.member 4 3).iff
    ((RankPredicateFormula.member 4 0).and (graphPreimageRelation.relabelSets ![1, 2, 4])))

theorem TransitiveClass.preimageMatrix_realize (M : TransitiveClass.{u})
    (domain graph target preimage : M.Element) :
    M.realize graphPreimageMatrix ![domain, graph, target, preimage] ↔
      preimage.val = ZFSet.sep (fun x => ∃ y, ZFSet.pair x y ∈ graph.val ∧ y ∈ target.val) domain.val := by
  have sem : M.realize graphPreimageMatrix ![domain, graph, target, preimage] ↔
      ∀ x : M.Element, x.val ∈ preimage.val ↔ x.val ∈ domain.val ∧
        ∃ y : M.Element, ZFSet.pair x.val y.val ∈ graph.val ∧ y.val ∈ target.val := by
    simp [graphPreimageMatrix, RankPredicateFormula.iff, M.realize_and, M.realize_relabel,
      TransitiveClass.realize, graphPreimageRelation, M.realize_ex, M.graphFormulaAtom_realize,
      iff_def, Fin.snoc, Function.comp_def]
  rw [sem]
  constructor
  · intro h
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_sep]
    constructor
    · intro hx
      obtain ⟨hd, y, edge, hy⟩ := (h (M.member preimage x hx)).mp hx
      exact ⟨hd, y.val, edge, hy⟩
    · rintro ⟨hd, y, edge, hy⟩
      exact (h (M.member domain x hd)).mpr ⟨hd, M.member target y hy, edge, hy⟩
  · intro h x
    rw [h, ZFSet.mem_sep]
    constructor
    · rintro ⟨hd, y, edge, hy⟩
      exact ⟨hd, M.member target y hy, edge, hy⟩
    · rintro ⟨hd, y, edge, hy⟩
      exact ⟨hd, y.val, edge, hy⟩

theorem TransitiveClass.ElementaryMap.preimage_iff {M N : TransitiveClass.{u}}
    (j : M.ElementaryMap N) (domain graph target preimage : M.Element) :
    (j preimage).val = ZFSet.sep
      (fun x => ∃ y, ZFSet.pair x y ∈ (j graph).val ∧ y ∈ (j target).val) (j domain).val ↔
      preimage.val = ZFSet.sep
        (fun x => ∃ y, ZFSet.pair x y ∈ graph.val ∧ y ∈ target.val) domain.val := by
  have h := j.realize_iff graphPreimageMatrix ![domain, graph, target, preimage]
  have args : j ∘ ![domain, graph, target, preimage] = ![j domain, j graph, j target, j preimage] := by
    funext i; fin_cases i <;> rfl
  rwa [args, M.preimageMatrix_realize, N.preimageMatrix_realize] at h

namespace ModelStage

noncomputable def graphPreimage (stage : ModelStage.{u}) (domain graph target : stage.model.Element) :
    stage.model.Element := stage.separation graphPreimageRelation ![graph, target] domain

theorem mem_graphPreimage (stage : ModelStage.{u}) (domain graph target x : stage.model.Element) :
    x.val ∈ (stage.graphPreimage domain graph target).val ↔ x.val ∈ domain.val ∧
      ∃ y : stage.model.Element, ZFSet.pair x.val y.val ∈ graph.val ∧ y.val ∈ target.val := by
  rw [graphPreimage, stage.mem_separation, graphPreimageRelation_realize]

theorem graphPreimage_val (stage : ModelStage.{u}) (domain graph target : stage.model.Element) :
    (stage.graphPreimage domain graph target).val =
      ZFSet.sep (fun x => ∃ y, ZFSet.pair x y ∈ graph.val ∧ y ∈ target.val) domain.val := by
  apply ZFSet.ext
  intro x
  rw [ZFSet.mem_sep]
  constructor
  · intro hx
    obtain ⟨hd, y, edge, hy⟩ := (stage.mem_graphPreimage domain graph target
      (stage.model.member (stage.graphPreimage domain graph target) x hx)).mp hx
    exact ⟨hd, y.val, edge, hy⟩
  · rintro ⟨hd, y, edge, hy⟩
    exact (stage.mem_graphPreimage domain graph target (stage.model.member domain x hd)).mpr
      ⟨hd, stage.model.member target y hy, edge, hy⟩

end ModelStage
end IBLP
