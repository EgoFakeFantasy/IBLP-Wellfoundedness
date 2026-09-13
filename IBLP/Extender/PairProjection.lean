import IBLP.Extender.Projection
import IBLP.Model.PairCoordinate
import IBLP.Model.InaccessibleAbsolute

namespace IBLP.Extender
open FullMarkedBLP
universe u

namespace Derivation
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}

noncomputable def IndexMap.ofFunction (limit : Order.IsSuccLimit alpha) (graph : stage.model.Element)
    (function : ZFSet.IsFunc (stage.hierarchy alpha).val (stage.hierarchy alpha).val graph.val) :
    IndexMap stage alpha where
  graph := ⟨graph.val, graph.property, Order.lt_succ_of_le
    (graph_rank_le_limit limit (stage.hierarchy_rank alpha).le (stage.hierarchy_rank alpha).le function.1)⟩
  function := function

theorem pairProjection_exists (limit : Order.IsSuccLimit alpha) (right : Bool) :
    ∃ graph : stage.model.Element,
      ZFSet.IsFunc (stage.hierarchy alpha).val (stage.hierarchy alpha).val graph.val ∧
      ∀ x y : stage.model.Element, ZFSet.pair x.val y.val ∈ graph.val ↔
        x.val ∈ (stage.hierarchy alpha).val ∧ pairCoordinate right x.val y.val := by
  classical
  have semantic (x y : stage.model.Element) :
      stage.model.realize (pairCoordinateFormula right) (Fin.snoc (Fin.snoc ![] x) y) ↔
        pairCoordinate right x.val y.val := by
    have args : Fin.snoc (Fin.snoc ![] x) y = ![x, y] := by
      funext i; fin_cases i <;> rfl
    rw [args, pairCoordinateFormula_realize]
  have total (x : stage.model.Element) (_ : x.val ∈ (stage.hierarchy alpha).val) :
      ∃ y : stage.model.Element,
        stage.model.realize (pairCoordinateFormula right) (Fin.snoc (Fin.snoc ![] x) y) := by
    by_cases hp : ∃ a b, x.val = ZFSet.pair a b
    · obtain ⟨a, b, same⟩ := hp
      have inside := stage.model.pair_components (same ▸ x.property)
      let a' : stage.model.Element := ⟨a, inside.1⟩
      let b' : stage.model.Element := ⟨b, inside.2⟩
      refine ⟨if right then b' else a', (semantic _ _).mpr (Or.inl ⟨a, b, same, ?_⟩)⟩
      cases right <;> rfl
    · exact ⟨stage.ordinal 0, (semantic _ _).mpr (Or.inr ⟨by simp [ModelStage.ordinal], hp⟩)⟩
  have bounded (x y : stage.model.Element) (hx : x.val ∈ (stage.hierarchy alpha).val)
      (hy : stage.model.realize (pairCoordinateFormula right) (Fin.snoc (Fin.snoc ![] x) y)) :
      y.val ∈ (stage.hierarchy alpha).val := by
    rcases (semantic _ _).mp hy with ⟨a, b, same, value⟩ | ⟨value, _⟩
    · have inside := pair_components_mem (stage.hierarchy_transitive alpha) (same ▸ hx)
      cases right <;> simp only [Bool.false_eq_true, ↓reduceIte] at value
      · exact value ▸ inside.1
      · exact value ▸ inside.2
    · apply (stage.mem_hierarchy_iff _ _).mpr
      simpa only [value, ZFSet.rank_empty] using limit.pos
  have unique (x y z : stage.model.Element) (_ : x.val ∈ (stage.hierarchy alpha).val)
      (hy : stage.model.realize (pairCoordinateFormula right) (Fin.snoc (Fin.snoc ![] x) y))
      (hz : stage.model.realize (pairCoordinateFormula right) (Fin.snoc (Fin.snoc ![] x) z)) : y = z :=
    Subtype.ext (pairCoordinate_unique ((semantic _ _).mp hy) ((semantic _ _).mp hz))
  obtain ⟨graph, function, edges⟩ := stage.definableGraph_exists (pairCoordinateFormula right) ![]
    (stage.hierarchy alpha) (stage.hierarchy alpha) total bounded unique
  exact ⟨graph, function, fun x y => (edges x y).trans (and_congr_right (fun _ => semantic x y))⟩

noncomputable def pairProjection (limit : Order.IsSuccLimit alpha) (right : Bool) : IndexMap stage alpha :=
  IndexMap.ofFunction limit (pairProjection_exists (stage := stage) limit right).choose
    (pairProjection_exists limit right).choose_spec.1

theorem pairProjection_edge_iff (limit : Order.IsSuccLimit alpha) (right : Bool)
    (x y : stage.model.Element) :
    ZFSet.pair x.val y.val ∈ (pairProjection (stage := stage) limit right).graph.val ↔
      x.val ∈ (stage.hierarchy alpha).val ∧ pairCoordinate right x.val y.val :=
  (pairProjection_exists limit right).choose_spec.2 x y

/-- A single finite formula records the entire coordinate graph. -/
def pairProjectionMatrix (right : Bool) : RankPredicateFormula 0 2 :=
  .all (.all ((rankFormulaGraphApplies 1 2 3).iff
    ((RankPredicateFormula.member 2 0).and ((pairCoordinateFormula right).relabelSets ![2, 3]))))

theorem pairProjectionMatrix_realize (M : TransitiveClass.{u}) (right : Bool) (domain graph : M.Element) :
    M.realize (pairProjectionMatrix right) ![domain, graph] ↔
      ∀ x y : M.Element, ZFSet.pair x.val y.val ∈ graph.val ↔
        x.val ∈ domain.val ∧ pairCoordinate right x.val y.val := by
  change (∀ x y, M.realize _ (Fin.snoc (Fin.snoc ![domain, graph] x) y)) ↔ _
  apply forall_congr'
  intro x
  apply forall_congr'
  intro y
  rw [M.pure_iff_realize, M.setGraphAtom_realize, M.realize_and, M.realize_relabel]
  have args : Fin.snoc (Fin.snoc ![domain, graph] x) y ∘ ![2, 3] = ![x, y] := by
    funext i; fin_cases i <;> rfl
  rw [args, pairCoordinateFormula_realize]
  rfl

theorem map_pairProjection_edge_iff (D : Derivation stage alpha beta)
    (limit : Order.IsSuccLimit alpha) (right : Bool)
    (x y : Test stage beta) :
    ZFSet.pair x.val y.val ∈ (D.map (pairProjection (stage := stage) limit right).graph).val ↔
      x.val ∈ (stage.hierarchy beta).val ∧ pairCoordinate right x.val y.val := by
  have source : (stage.model.rankPart (Order.succ alpha)).realize (pairProjectionMatrix right)
      ![top, (pairProjection (stage := stage) limit right).graph] := by
    apply (pairProjectionMatrix_realize _ _ _ _).mpr
    intro x y
    exact pairProjection_edge_iff limit right (stage.rankInclude _ x) (stage.rankInclude _ y)
  have image := (D.map.realize_iff (pairProjectionMatrix right)
    ![top, (pairProjection (stage := stage) limit right).graph]).mpr source
  have args : D.map ∘ ![top, (pairProjection (stage := stage) limit right).graph] =
      ![D.map top, D.map (pairProjection (stage := stage) limit right).graph] := by
    funext i; fin_cases i <;> rfl
  rw [args] at image
  have result := (pairProjectionMatrix_realize _ _ _ _).mp image x y
  change _ ↔ x.val ∈ (D.map (stage.rankHierarchy (endpoint alpha))).val ∧ _ at result
  rw [stage.boundedMap_top] at result
  exact result

noncomputable def pairSeed (limit : Order.IsSuccLimit beta) (a b : Seed stage beta) : Seed stage beta :=
  ⟨(stage.orderedPair (stage.rankInclude _ a) (stage.rankInclude _ b)).val,
    (stage.orderedPair (stage.rankInclude _ a) (stage.rankInclude _ b)).property, by
      rw [stage.orderedPair_val]
      exact rank_orderedPair_lt_of_limit limit a.property.2 b.property.2⟩

theorem pairSeed_val (limit : Order.IsSuccLimit beta) (a b : Seed stage beta) :
    (pairSeed limit a b).val = ZFSet.pair a.val b.val := stage.orderedPair_val _ _

theorem project_pairSeed (D : Derivation stage alpha beta)
    (ha : Order.IsSuccLimit alpha) (hb : Order.IsSuccLimit beta) (right : Bool) (a b : Seed stage beta) :
    D.project (pairProjection ha right) (pairSeed hb a b) = if right then b else a := by
  let seed := pairSeed hb a b
  let output := if right then b else a
  let seed' : Test stage beta := ⟨seed.val, seed.property.1, seed.property.2.trans (Order.lt_succ beta)⟩
  let output' : Test stage beta := ⟨output.val, output.property.1, output.property.2.trans (Order.lt_succ beta)⟩
  have edge := (D.map_pairProjection_edge_iff ha right seed' output').mpr
    ⟨(stage.mem_hierarchy beta seed.val).mpr seed.property, by
      change pairCoordinate right (pairSeed hb a b).val output.val
      rw [pairSeed_val, pairCoordinate_pair]
      cases right <;> rfl⟩
  exact Subtype.ext (D.project_unique (pairProjection ha right) seed output.val edge).symm

end Derivation
end IBLP.Extender
