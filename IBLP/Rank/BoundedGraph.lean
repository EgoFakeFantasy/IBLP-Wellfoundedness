import IBLP.Rank.Restriction
import FullMarkedBLP.RankRestrictionGraph
import FullMarkedBLP.RankCriticalLimit

namespace IBLP
open FullMarkedBLP

universe u

/-- 真正的集合图及两端集合结构的初等性。允许任意秩，包括后继秩。 -/
def GraphElementary {lambda : Ordinal.{u}} (graph : RankDomain lambda)
    (alpha beta : OrdinalDomain lambda) : Prop :=
  rankIsFunction graph (rankHierarchy alpha) (rankHierarchy beta) ∧
  ∀ (n : Nat) (phi : membershipLanguage.Formula (Fin n))
    (xs : Fin n → RankDomain alpha.val) (ys : Fin n → RankDomain beta.val),
    (∀ i, rankGraphApplies graph (rankInclude alpha.property.le (xs i))
      (rankInclude beta.property.le (ys i))) →
    (phi.Realize ys ↔ phi.Realize xs)

theorem GraphElementary.output_exists {lambda : Ordinal.{u}}
    {graph : RankDomain lambda} {alpha beta : OrdinalDomain lambda}
    (h : GraphElementary graph alpha beta) (x : RankDomain alpha.val) :
    ∃ y : RankDomain beta.val, rankGraphApplies graph (rankInclude alpha.property.le x)
      (rankInclude beta.property.le y) := by
  obtain ⟨y, hy, hedge, _⟩ := h.1.2 (rankInclude alpha.property.le x)
    (ZFSet.mem_vonNeumann.mpr x.property)
  exact ⟨⟨y.val, ZFSet.mem_vonNeumann.mp hy⟩, hedge⟩

noncomputable def GraphElementary.value {lambda : Ordinal.{u}}
    {graph : RankDomain lambda} {alpha beta : OrdinalDomain lambda}
    (h : GraphElementary graph alpha beta) (x : RankDomain alpha.val) : RankDomain beta.val :=
  (h.output_exists x).choose

theorem GraphElementary.value_applies {lambda : Ordinal.{u}}
    {graph : RankDomain lambda} {alpha beta : OrdinalDomain lambda}
    (h : GraphElementary graph alpha beta) (x : RankDomain alpha.val) :
    rankGraphApplies graph (rankInclude alpha.property.le x)
      (rankInclude beta.property.le (h.value x)) := (h.output_exists x).choose_spec

/-- 从图本身恢复映射；不要求它来自环境的全域自嵌入。 -/
noncomputable def GraphElementary.toEmbedding {lambda : Ordinal.{u}}
    {graph : RankDomain lambda} {alpha beta : OrdinalDomain lambda}
    (h : GraphElementary graph alpha beta) :
    FirstOrder.Language.ElementaryEmbedding membershipLanguage
      (RankDomain alpha.val) (RankDomain beta.val) where
  toFun := h.value
  map_formula' := fun n phi xs => h.2 n phi xs (h.value ∘ xs) (fun i => h.value_applies (xs i))

noncomputable def boundedGraph {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j : RankElementaryEmbedding lambda) (alpha : OrdinalDomain lambda) : RankDomain lambda :=
  rankRestrictionGraph hl j (rankHierarchy alpha)

theorem boundedGraph_applies_iff {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j : RankElementaryEmbedding lambda) (alpha : OrdinalDomain lambda)
    (x y : RankDomain lambda) :
    rankGraphApplies (boundedGraph hl j alpha) x y ↔ x.val.rank < alpha.val ∧ j x = y := by
  rw [boundedGraph, rankRestrictionGraph_applies_iff]
  simp only [rankHierarchy, ZFSet.mem_vonNeumann]

theorem boundedGraph_elementary {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j : RankElementaryEmbedding lambda) (alpha : OrdinalDomain lambda) :
    GraphElementary (boundedGraph hl j alpha) alpha (rankOrdinalAction j alpha) := by
  constructor
  · rw [← rankElementary_hierarchy hl j alpha]
    exact rankRestrictionGraph_isFunction hl j (rankHierarchy alpha)
  · intro n phi xs ys edges
    have same : ys = rankRestrict hl j alpha ∘ xs := by
      funext i
      apply Subtype.ext
      exact (congrArg Subtype.val ((boundedGraph_applies_iff hl j alpha _ _).mp (edges i)).2).symm
    rw [same]
    exact (rankRestrict hl j alpha).map_formula phi xs

def ordinalSuccessor {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (alpha : OrdinalDomain lambda) : OrdinalDomain lambda :=
  ⟨Order.succ alpha.val, hl.succ_lt alpha.property⟩

theorem ordinalAction_successor {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j : RankElementaryEmbedding lambda) (alpha : OrdinalDomain lambda) :
    rankOrdinalAction j (ordinalSuccessor hl alpha) =
      ordinalSuccessor hl (rankOrdinalAction j alpha) :=
  Subtype.ext (rankOrdinalAction_succ hl j alpha)

theorem boundedGraph_successor_elementary {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j : RankElementaryEmbedding lambda) (alpha : OrdinalDomain lambda) :
    GraphElementary (boundedGraph hl j (ordinalSuccessor hl alpha))
      (ordinalSuccessor hl alpha) (ordinalSuccessor hl (rankOrdinalAction j alpha)) := by
  rw [← ordinalAction_successor hl j alpha]
  exact boundedGraph_elementary hl j (ordinalSuccessor hl alpha)

/-- 临界点定义直接读取集合图；后续模型不需要保留一个全域 owner。 -/
def GraphCriticalPoint {lambda : Ordinal.{u}} (graph : RankDomain lambda)
    (c : OrdinalDomain lambda) : Prop :=
  (∃ y, rankGraphApplies graph (ordinalDomainElement c) y ∧ y ≠ ordinalDomainElement c) ∧
  ∀ a : OrdinalDomain lambda, a < c →
    rankGraphApplies graph (ordinalDomainElement a) (ordinalDomainElement a)

theorem boundedGraph_successor_criticalPoint {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {j : RankElementaryEmbedding lambda}
    {c alpha : OrdinalDomain lambda} (hc : RankCriticalPoint j c) (hca : c ≤ alpha) :
    GraphCriticalPoint (boundedGraph hl j (ordinalSuccessor hl alpha)) c := by
  constructor
  · refine ⟨j (ordinalDomainElement c), ?_, ?_⟩
    · apply (boundedGraph_applies_iff hl j _ _ _).mpr
      refine ⟨?_, rfl⟩
      simpa only [ordinalDomainElement, Ordinal.rank_toZFSet, ordinalSuccessor] using
        (Order.lt_succ_of_le hca : c.val < Order.succ alpha.val)
    · intro same
      apply hc.1
      apply Subtype.ext
      exact (congrArg (fun x : RankDomain lambda => x.val.rank) same).trans (Ordinal.rank_toZFSet c.val)
  · intro a ha
    apply (boundedGraph_applies_iff hl j _ _ _).mpr
    constructor
    · simpa only [ordinalDomainElement, Ordinal.rank_toZFSet, ordinalSuccessor] using
        (Order.lt_succ_of_le (ha.le.trans hca) : a.val < Order.succ alpha.val)
    · rw [← ordinalDomainElement_action, hc.2 a ha]

theorem boundedGraph_successor_ordinal_edge {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) (j : RankElementaryEmbedding lambda)
    (alpha eta zeta : OrdinalDomain lambda) (heta : eta ≤ alpha)
    (hedge : rankOrdinalAction j eta = zeta) :
    rankGraphApplies (boundedGraph hl j (ordinalSuccessor hl alpha))
      (ordinalDomainElement eta) (ordinalDomainElement zeta) := by
  apply (boundedGraph_applies_iff hl j _ _ _).mpr
  constructor
  · simpa only [ordinalDomainElement, Ordinal.rank_toZFSet, ordinalSuccessor] using
      (Order.lt_succ_of_le heta : eta.val < Order.succ alpha.val)
  · rw [← ordinalDomainElement_action, hedge]

end IBLP
