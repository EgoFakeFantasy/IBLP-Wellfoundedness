import IBLP.Extender.NaturalTests
import IBLP.Model.GraphRead
import IBLP.Model.CountableRankBound

namespace IBLP.Extender.Derivation
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}

theorem readIndex_exists (n : Nat) : ∃ graph : stage.model.Element,
    ZFSet.IsFunc (stage.hierarchy alpha).val (stage.hierarchy alpha).val graph.val ∧
      ∀ x y : stage.model.Element, ZFSet.pair x.val y.val ∈ graph.val ↔
        x.val ∈ (stage.hierarchy alpha).val ∧ graphReadValue (n : Ordinal.{u}).toZFSet x.val y.val := by
  let index := stage.ordinal (n : Ordinal.{u})
  have args (x y : stage.model.Element) : Fin.snoc (Fin.snoc ![index] x) y = ![index, x, y] := by
    funext i; fin_cases i <;> rfl
  have total (x : stage.model.Element) (_ : x.val ∈ (stage.hierarchy alpha).val) :
      ∃ y : stage.model.Element, stage.model.realize graphReadRelation (Fin.snoc (Fin.snoc ![index] x) y) :=
    ⟨stage.graphRead index x, by rw [args]; exact stage.graphRead_satisfies index x⟩
  have bounded (x y : stage.model.Element) (hx : x.val ∈ (stage.hierarchy alpha).val)
      (hy : stage.model.realize graphReadRelation (Fin.snoc (Fin.snoc ![index] x) y)) :
      y.val ∈ (stage.hierarchy alpha).val := by
    rw [args] at hy
    rw [stage.graphRead_unique index x y hy]
    exact (stage.mem_hierarchy_iff _ _).mpr
      ((stage.graphRead_rank_le index x).trans_lt ((stage.mem_hierarchy_iff _ _).mp hx))
  have unique (x y z : stage.model.Element) (_ : x.val ∈ (stage.hierarchy alpha).val)
      (hy : stage.model.realize graphReadRelation (Fin.snoc (Fin.snoc ![index] x) y))
      (hz : stage.model.realize graphReadRelation (Fin.snoc (Fin.snoc ![index] x) z)) : y = z := by
    rw [args] at hy hz
    exact (stage.graphRead_unique index x y hy).trans (stage.graphRead_unique index x z hz).symm
  obtain ⟨graph, function, edges⟩ := stage.definableGraph_exists graphReadRelation ![index]
    (stage.hierarchy alpha) (stage.hierarchy alpha) total bounded unique
  refine ⟨graph, function, fun x y => ?_⟩
  rw [edges, args, graphReadRelation_absolute]
  rfl

noncomputable def readIndex (ha : Order.IsSuccLimit alpha) (n : Nat) : IndexMap stage alpha :=
  IndexMap.ofFunction ha (readIndex_exists n).choose (readIndex_exists n).choose_spec.1

theorem readIndex_edge_iff (ha : Order.IsSuccLimit alpha) (n : Nat) (x y : stage.model.Element) :
    ZFSet.pair x.val y.val ∈ (readIndex (stage := stage) ha n).graph.val ↔
      x.val ∈ (stage.hierarchy alpha).val ∧ graphReadValue (n : Ordinal.{u}).toZFSet x.val y.val :=
  (readIndex_exists n).choose_spec.2 x y

def readIndexMatrix : RankPredicateFormula 0 3 :=
  .all (.all ((rankFormulaGraphApplies 2 3 4).iff
    ((RankPredicateFormula.member 3 0).and (graphReadRelation.relabelSets ![1, 3, 4]))))

theorem readIndexMatrix_realize (M : TransitiveClass.{u}) (domain index graph : M.Element) :
    M.realize readIndexMatrix ![domain, index, graph] ↔
      ∀ x y : M.Element, ZFSet.pair x.val y.val ∈ graph.val ↔
        x.val ∈ domain.val ∧ graphReadValue index.val x.val y.val := by
  change (∀ x y, M.realize _ (Fin.snoc (Fin.snoc ![domain, index, graph] x) y)) ↔ _
  apply forall_congr'
  intro x
  apply forall_congr'
  intro y
  rw [M.pure_iff_realize, M.realize_and, M.setGraphAtom_realize, M.realize_relabel]
  have args : Fin.snoc (Fin.snoc ![domain, index, graph] x) y ∘ ![1, 3, 4] = ![index, x, y] := by
    funext i; fin_cases i <;> rfl
  rw [args, graphReadRelation_absolute]
  rfl

theorem map_readIndex_edge_iff (D : Derivation stage alpha beta)
    (ha : Order.IsSuccLimit alpha) (hb : Order.IsSuccLimit beta) (n : Nat) (x y : Test stage beta) :
    ZFSet.pair x.val y.val ∈ (D.map (readIndex ha n).graph).val ↔
      x.val ∈ (stage.hierarchy beta).val ∧ graphReadValue (n : Ordinal.{u}).toZFSet x.val y.val := by
  have source : (stage.model.rankPart (Order.succ alpha)).realize readIndexMatrix
      ![top, naturalTest ha n, (readIndex ha n).graph] := by
    apply (readIndexMatrix_realize _ _ _ _).mpr
    intro x y
    exact readIndex_edge_iff ha n (stage.rankInclude _ x) (stage.rankInclude _ y)
  have image := (D.map.realize_iff readIndexMatrix ![top, naturalTest ha n, (readIndex ha n).graph]).mpr source
  have args : D.map ∘ ![top, naturalTest ha n, (readIndex ha n).graph] =
      ![D.map top, D.map (naturalTest ha n), D.map (readIndex ha n).graph] := by
    funext i; fin_cases i <;> rfl
  rw [args, D.map_naturalTest ha hb, readIndexMatrix_realize] at image
  have h := image x y
  change _ ↔ x.val ∈ (D.map (stage.rankHierarchy (endpoint alpha))).val ∧ _ at h
  rwa [stage.boundedMap_top] at h

end IBLP.Extender.Derivation
