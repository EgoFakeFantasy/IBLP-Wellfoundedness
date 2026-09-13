import IBLP.Rank.RootOwners
import IBLP.Rank.BoundedGraph

namespace IBLP
open FullMarkedBLP

universe u

def rootEndpoint (r : Nat) : Nat :=
  ((IBLP.rowAt IBLP.root r).bind IBLP.Row.e).getD 0

theorem rootEndpoint_eq {r e : Nat} {row : IBLP.Row}
    (hr : IBLP.rowAt IBLP.root r = some row) (he : row.e = some e) : rootEndpoint r = e := by
  simp [rootEndpoint, hr, he]

theorem root_endpoint_edge {r e : Nat} {row : IBLP.Row}
    (hr : IBLP.rowAt IBLP.root r = some row) (he : row.e = some e) :
    (e, r + 1) ∈ row.edgePairs r := by
  have hp := IBLP.rowAt_pos hr
  have hle : r ≤ 6 := IBLP.rowAt_le_length hr
  interval_cases r <;> norm_num [IBLP.rowAt, IBLP.root] at hr <;> subst row <;>
    norm_num [IBLP.Row.e, fromRight] at he <;> subst e <;> decide

theorem root_edge_source_le {r e : Nat} {row : IBLP.Row}
    (hr : IBLP.rowAt IBLP.root r = some row) (he : row.e = some e) :
    ∀ edge ∈ row.edgePairs r, edge.1 ≤ e := by
  have hp := IBLP.rowAt_pos hr
  have hle : r ≤ 6 := IBLP.rowAt_le_length hr
  interval_cases r <;> norm_num [IBLP.rowAt, IBLP.root] at hr <;> subst row <;>
    norm_num [IBLP.Row.e, fromRight] at he <;> subst e <;> simp [Row.edgePairs]

theorem root_minimum_le_endpoint {r e minimum : Nat} {row : IBLP.Row}
    (hr : IBLP.rowAt IBLP.root r = some row) (he : row.e = some e)
    (hm : row.columns.head? = some minimum) : minimum ≤ e := by
  have hp := IBLP.rowAt_pos hr
  have hle : r ≤ 6 := IBLP.rowAt_le_length hr
  interval_cases r <;> norm_num [IBLP.rowAt, IBLP.root] at hr <;> subst row <;>
    norm_num [IBLP.Row.e, fromRight] at he hm <;> omega

noncomputable def rootGraph {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j : RankElementaryEmbedding lambda) (c : OrdinalDomain lambda) (r : Nat) : RankDomain lambda :=
  boundedGraph hl (rootOwner hl j r) (ordinalSuccessor hl (rankCriticalSequence j c (rootEndpoint r)))

/-- 六行根的有界语义：保存整个后继秩，且全部有限边和临界点由实际集合图实现。 -/
def RootGraphRealization {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (theta : Nat → OrdinalDomain lambda) (graphs : Nat → RankDomain lambda) : Prop :=
  StrictMono theta ∧ (∀ i, ∃ k : Cardinal.{u}, k.ord = (theta i).val) ∧
  (∀ i, Cardinal.IsInaccessible (theta i).val.card) ∧
  ∀ r row e, IBLP.rowAt IBLP.root r = some row → row.e = some e →
    GraphElementary (graphs r) (ordinalSuccessor hl (theta e))
      (ordinalSuccessor hl (theta (r + 1))) ∧
    (∀ minimum, row.columns.head? = some minimum → GraphCriticalPoint (graphs r) (theta minimum)) ∧
    (∀ edge ∈ row.edgePairs r, rankGraphApplies (graphs r)
      (ordinalDomainElement (theta edge.1)) (ordinalDomainElement (theta edge.2)))

theorem rootGraph_realization {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {j : RankElementaryEmbedding lambda} {c : OrdinalDomain lambda} (hc : RankCriticalPoint j c) :
    RootGraphRealization hl (rankCriticalSequence j c) (rootGraph hl j c) := by
  refine ⟨rankCriticalSequence_strictMono hc, rankCriticalSequence_cardinal hl hc,
    rankCriticalSequence_isInaccessible hl hc, ?_⟩
  intro r row e hr he
  have endpoint := (rootOwner_edges hl j c hr) (e, r + 1) (root_endpoint_edge hr he)
  dsimp only [Prod.fst, Prod.snd] at endpoint
  have graphEq : rootGraph hl j c r =
      boundedGraph hl (rootOwner hl j r) (ordinalSuccessor hl (rankCriticalSequence j c e)) := by
    rw [rootGraph, rootEndpoint_eq hr he]
  rw [graphEq]
  refine ⟨?_, ?_, ?_⟩
  · rw [← endpoint]
    exact boundedGraph_successor_elementary hl (rootOwner hl j r) _
  · intro minimum hm
    exact boundedGraph_successor_criticalPoint hl (rootOwner_criticalPoint hl hc hr hm)
      ((rankCriticalSequence_strictMono hc).monotone (root_minimum_le_endpoint hr he hm))
  · intro edge hedge
    exact boundedGraph_successor_ordinal_edge hl (rootOwner hl j r) _ _ _
      ((rankCriticalSequence_strictMono hc).monotone (root_edge_source_le hr he edge hedge))
      (rootOwner_edges hl j c hr edge hedge)

theorem exists_root_graphs_of_i3 (h : I3.{u}) :
    ∃ (lambda : Ordinal.{u}) (hl : Order.IsSuccLimit lambda)
      (theta : Nat → OrdinalDomain lambda) (graphs : Nat → RankDomain lambda),
      RootGraphRealization hl theta graphs := by
  obtain ⟨lambda, hl, j, c, hc⟩ := i3_iff_criticalPoint.mp h
  exact ⟨lambda, hl, rankCriticalSequence j c, rootGraph hl j c, rootGraph_realization hl hc⟩

end IBLP
