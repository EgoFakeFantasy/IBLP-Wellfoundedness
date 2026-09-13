import IBLP.Model.Replacement

namespace IBLP
open FullMarkedBLP
universe u

/-- A functional finite formula determines a complete graph belonging to M.
The graph is constructed by the already proved internal choice scheme. -/
theorem ModelStage.definableGraph_exists (stage : ModelStage.{u}) {n : Nat}
    (phi : RankPredicateFormula 0 (n + 2)) (values : Fin n → stage.model.Element)
    (domain range : stage.model.Element)
    (total : ∀ x : stage.model.Element, x.val ∈ domain.val →
      ∃ y : stage.model.Element, stage.model.realize phi (Fin.snoc (Fin.snoc values x) y))
    (bounded : ∀ x y : stage.model.Element, x.val ∈ domain.val →
      stage.model.realize phi (Fin.snoc (Fin.snoc values x) y) → y.val ∈ range.val)
    (unique : ∀ x y z : stage.model.Element, x.val ∈ domain.val →
      stage.model.realize phi (Fin.snoc (Fin.snoc values x) y) →
      stage.model.realize phi (Fin.snoc (Fin.snoc values x) z) → y = z) :
    ∃ graph : stage.model.Element, ZFSet.IsFunc domain.val range.val graph.val ∧
      ∀ x y : stage.model.Element, ZFSet.pair x.val y.val ∈ graph.val ↔
        x.val ∈ domain.val ∧ stage.model.realize phi (Fin.snoc (Fin.snoc values x) y) := by
  let choice := stage.choiceFunction phi values domain total
  have edges (x y : stage.model.Element) : ZFSet.pair x.val y.val ∈ choice.graph.val ↔
      x.val ∈ domain.val ∧ stage.model.realize phi (Fin.snoc (Fin.snoc values x) y) := by
    constructor
    · intro edge
      exact ⟨(ZFSet.pair_mem_prod.mp (choice.isFunction.1 edge)).1, choice.satisfies x y edge⟩
    · rintro ⟨hx, hxy⟩
      have hy : choice.value x hx = y := unique x _ y hx (choice.value_realizes x hx) hxy
      simpa only [hy] using choice.value_graph x hx
  refine ⟨choice.graph, ⟨?_, choice.isFunction.2⟩, edges⟩
  intro p hp
  obtain ⟨x, hx, y, hy, pair⟩ := ZFSet.mem_prod.mp (choice.isFunction.1 hp)
  have edge : ZFSet.pair x y ∈ choice.graph.val := by simpa only [pair] using hp
  let x' := stage.model.member domain x hx
  let y' := stage.model.member choice.range y hy
  have hphi := (edges x' y').mp edge
  exact ZFSet.mem_prod.mpr ⟨x, hx, y, bounded x' y' hx hphi.2, pair⟩

end IBLP
