import IBLP.Extender.CodeMemberFormula
import IBLP.Extender.LocalClosure

namespace IBLP.Extender
open FullMarkedBLP Derivation
universe u

def localRelationBody : RankPredicateFormula 0 7 :=
  codeMemberFormula.relabelSets ![0, 1, 2, 3, 5, 6]

theorem localRelationBody_realize (M : TransitiveClass.{u}) (v : Fin 7 → M.Element) :
    M.realize localRelationBody v ↔ M.realize codeMemberFormula ![v 0, v 1, v 2, v 3, v 5, v 6] := by
  rw [localRelationBody, M.realize_relabel]
  have args : v ∘ ![0, 1, 2, 3, 5, 6] = ![v 0, v 1, v 2, v 3, v 5, v 6] := by
    funext i; fin_cases i <;> rfl
  rw [args]

def localRelationFormula : RankPredicateFormula 0 5 :=
  ((rankFormulaOrderedPair 4 5 6).and localRelationBody).ex.ex

theorem localRelationFormula_realize (M : TransitiveClass.{u}) (U K p q z : M.Element) :
    M.realize localRelationFormula (Fin.snoc ![U, K, p, q] z) ↔
      ∃ c d : M.Element, z.val = ZFSet.pair c.val d.val ∧ M.realize codeMemberFormula ![U, K, p, q, c, d] := by
  simp [localRelationFormula, M.realize_ex, M.realize_and, M.setOrderedPairAtom_realize,
    localRelationBody_realize]

namespace LocalCodes
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}
  (D : Derivation stage alpha beta) (ha : Order.IsSuccLimit alpha) (hb : Order.IsSuccLimit beta)
  (bound : stage.model.Element)

noncomputable def relation : stage.model.Element :=
  stage.separation localRelationFormula
    ![stage.hierarchy alpha, D.graph, stage.rankInclude _ (pairProjection ha false).graph,
      stage.rankInclude _ (pairProjection ha true).graph]
    (stage.product (domain stage alpha beta bound) (domain stage alpha beta bound))

theorem relation_iff (c d : SetDomain (domain stage alpha beta bound).val) :
    setRelation (domain stage alpha beta bound).val (relation D ha bound).val c d ↔
      Ultrapower.Mem D ha hb (decode D ha hb bound c) (decode D ha hb bound d) := by
  change ZFSet.pair c.val d.val ∈ (relation D ha bound).val ↔ _
  have pairEq := stage.orderedPair_val (element bound c) (element bound d)
  change (stage.orderedPair (element bound c) (element bound d)).val = ZFSet.pair c.val d.val at pairEq
  rw [← pairEq, relation, stage.mem_separation, localRelationFormula_realize]
  have inside : (stage.orderedPair (element bound c) (element bound d)).val ∈
      (stage.product (domain stage alpha beta bound) (domain stage alpha beta bound)).val := by
    rw [stage.product_val, pairEq, ZFSet.pair_mem_prod]
    exact ⟨c.property, d.property⟩
  rw [and_iff_right inside]
  change (∃ x y : stage.model.Element, _ ∧ _) ↔ GlobalTruth.Member D ha hb _ _
  rw [← codeMember_iff D ha hb bound c d]
  constructor
  · rintro ⟨x, y, he, h⟩
    rw [pairEq] at he
    obtain ⟨hx, hy⟩ := ZFSet.pair_inj.mp he
    have xe : x = element bound c := Subtype.ext hx.symm
    have ye : y = element bound d := Subtype.ext hy.symm
    rwa [xe, ye] at h
  · intro h
    exact ⟨element bound c, element bound d, pairEq, h⟩

end LocalCodes
end IBLP.Extender
