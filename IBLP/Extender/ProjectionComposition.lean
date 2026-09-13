import IBLP.Extender.PairProjection

namespace IBLP.Extender
open FullMarkedBLP
universe u

namespace Derivation
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}

noncomputable def IndexMap.comp (limit : Order.IsSuccLimit alpha) (p q : IndexMap stage alpha) :
    IndexMap stage alpha :=
  IndexMap.ofFunction limit
    (stage.compGraph (stage.rankInclude _ p.graph) (stage.rankInclude _ q.graph)
      (stage.hierarchy alpha) (stage.hierarchy alpha) (stage.hierarchy alpha) (stage.hierarchy alpha)
      p.function q.function (fun _ h => h))
    (stage.compGraph_function _ _ _ _ _ _ p.function q.function (fun _ h => h))

theorem IndexMap.comp_edge_iff (limit : Order.IsSuccLimit alpha) (p q : IndexMap stage alpha)
    (x z : ZFSet.{u}) :
    ZFSet.pair x z ∈ (p.comp limit q).graph.val ↔
      ∃ y, ZFSet.pair x y ∈ p.graph.val ∧ ZFSet.pair y z ∈ q.graph.val :=
  stage.compGraph_edge_iff _ _ _ _ _ _ p.function q.function (fun _ h => h) x z

def indexCompositionMatrix : RankPredicateFormula 0 3 :=
  .all (.all ((rankFormulaGraphApplies 2 3 4).iff
    (graphCompRelation.relabelSets ![0, 1, 3, 4])))

theorem indexCompositionMatrix_realize (M : TransitiveClass.{u}) (p q composite : M.Element) :
    M.realize indexCompositionMatrix ![p, q, composite] ↔
      ∀ x z : M.Element, ZFSet.pair x.val z.val ∈ composite.val ↔
        ∃ y : ZFSet.{u}, ZFSet.pair x.val y ∈ p.val ∧ ZFSet.pair y z.val ∈ q.val := by
  have sem : M.realize indexCompositionMatrix ![p, q, composite] ↔
      ∀ x z : M.Element, ZFSet.pair x.val z.val ∈ composite.val ↔
        ∃ y : M.Element, ZFSet.pair x.val y.val ∈ p.val ∧ ZFSet.pair y.val z.val ∈ q.val := by
    change (∀ x z, M.realize _ (Fin.snoc (Fin.snoc ![p, q, composite] x) z)) ↔ _
    apply forall_congr'
    intro x
    apply forall_congr'
    intro z
    rw [M.pure_iff_realize, M.setGraphAtom_realize, M.realize_relabel]
    have args : Fin.snoc (Fin.snoc ![p, q, composite] x) z ∘ ![0, 1, 3, 4] =
        Fin.snoc (Fin.snoc ![p, q] x) z := by
      funext i; fin_cases i <;> rfl
    rw [args, graphCompRelation_realize]
    rfl
  rw [sem]
  apply forall_congr'
  intro x
  apply forall_congr'
  intro z
  apply iff_congr Iff.rfl
  constructor
  · rintro ⟨y, hp, hq⟩; exact ⟨y.val, hp, hq⟩
  · rintro ⟨y, hp, hq⟩
    exact ⟨⟨y, (M.pair_components (M.transitive hp p.property)).2⟩, hp, hq⟩

theorem map_comp_edge_iff (D : Derivation stage alpha beta) (limit : Order.IsSuccLimit alpha)
    (p q : IndexMap stage alpha) (x z : Test stage beta) :
    ZFSet.pair x.val z.val ∈ (D.map (p.comp limit q).graph).val ↔
      ∃ y, ZFSet.pair x.val y ∈ (D.map p.graph).val ∧ ZFSet.pair y z.val ∈ (D.map q.graph).val := by
  have source : (stage.model.rankPart (Order.succ alpha)).realize indexCompositionMatrix
      ![p.graph, q.graph, (p.comp limit q).graph] := by
    apply (indexCompositionMatrix_realize _ _ _ _).mpr
    intro x z
    exact p.comp_edge_iff limit q x.val z.val
  have image := (D.map.realize_iff indexCompositionMatrix ![p.graph, q.graph, (p.comp limit q).graph]).mpr source
  have args : D.map ∘ ![p.graph, q.graph, (p.comp limit q).graph] =
      ![D.map p.graph, D.map q.graph, D.map (p.comp limit q).graph] := by
    funext i; fin_cases i <;> rfl
  rw [args] at image
  exact (indexCompositionMatrix_realize _ _ _ _).mp image x z

theorem project_comp (D : Derivation stage alpha beta) (limit : Order.IsSuccLimit alpha)
    (p q : IndexMap stage alpha) (seed : Seed stage beta) :
    D.project (p.comp limit q) seed = D.project q (D.project p seed) := by
  let output := D.project q (D.project p seed)
  let seed' : Test stage beta := ⟨seed.val, seed.property.1, seed.property.2.trans (Order.lt_succ beta)⟩
  let output' : Test stage beta := ⟨output.val, output.property.1, output.property.2.trans (Order.lt_succ beta)⟩
  have edge := (D.map_comp_edge_iff limit p q seed' output').mpr
    ⟨(D.project p seed).val, D.project_edge p seed, D.project_edge q (D.project p seed)⟩
  exact Subtype.ext (D.project_unique (p.comp limit q) seed output.val edge).symm

end Derivation
end IBLP.Extender
