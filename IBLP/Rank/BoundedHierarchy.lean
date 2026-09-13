import IBLP.Rank.HierarchyGraph
import IBLP.Rank.WeakAction
import FullMarkedBLP.RankNontrivialFormula

namespace IBLP
open FullMarkedBLP

universe u

theorem rankMap_predicate {lambda mu : Ordinal.{u}} (j : RankMap lambda mu)
    {n : Nat} (phi : RankPredicateFormula 0 n) (values : Fin n → RankDomain lambda) :
    phi.Realize Fin.elim0 (j ∘ values) ↔ phi.Realize Fin.elim0 values := by
  rw [rankPredicateToFormula_realize, rankPredicateToFormula_realize]
  exact j.map_formula _ values

def endpoint (alpha : Ordinal.{u}) : OrdinalDomain (Order.succ alpha) := ⟨alpha, Order.lt_succ alpha⟩

def largestSetFormula : RankPredicateFormula 0 1 := .all (.all (.imp (.member 2 1) (.member 2 0)))

theorem largestSetFormula_realize {alpha : Ordinal.{u}} (top : RankDomain (Order.succ alpha)) :
    largestSetFormula.Realize Fin.elim0 ![top] ↔ top.val = ZFSet.vonNeumann alpha := by
  have semantics : largestSetFormula.Realize Fin.elim0 ![top] ↔
      ∀ x y : RankDomain (Order.succ alpha), y.val ∈ x.val → y.val ∈ top.val := by
    simp [largestSetFormula, RankPredicateFormula.Realize, Fin.snoc]
  rw [semantics]
  constructor
  · intro h
    apply ZFSet.ext
    intro z
    constructor
    · intro hz
      exact ZFSet.subset_vonNeumann.mpr (Order.lt_succ_iff.mp top.property) hz
    · intro hz
      have hr := ZFSet.mem_vonNeumann.mp hz
      let z' : RankDomain (Order.succ alpha) := ⟨z, hr.trans (Order.lt_succ alpha)⟩
      let singleton : RankDomain (Order.succ alpha) := ⟨{z}, by
        rw [ZFSet.rank_singleton]
        exact Order.lt_succ_of_le (Order.succ_le_of_lt hr)⟩
      exact h singleton z' (by simp [singleton, z'])
  · intro same x y hy
    rw [same]
    exact ZFSet.subset_vonNeumann.mpr (Order.lt_succ_iff.mp x.property) hy

theorem boundedMap_top {alpha beta : Ordinal.{u}} (k : BoundedMap alpha beta) :
    k (rankHierarchy (endpoint alpha)) = rankHierarchy (endpoint beta) := by
  have h := rankMap_predicate k largestSetFormula ![rankHierarchy (endpoint alpha)]
  have same : k ∘ ![rankHierarchy (endpoint alpha)] = ![k (rankHierarchy (endpoint alpha))] := by
    funext i; fin_cases i; rfl
  rw [same, largestSetFormula_realize, largestSetFormula_realize] at h
  exact Subtype.ext (h.mpr rfl)

def largestOrdinalFormula : RankPredicateFormula 0 1 :=
  (rankFormulaOrdinal 0).and
    (.all ((rankFormulaOrdinal 1).imp ((RankPredicateFormula.member 1 0).or (.equal 1 0))))

theorem largestOrdinalFormula_realize {alpha : Ordinal.{u}} (top : RankDomain (Order.succ alpha)) :
    largestOrdinalFormula.Realize Fin.elim0 ![top] ↔ top.val = alpha.toZFSet := by
  have semantics : largestOrdinalFormula.Realize Fin.elim0 ![top] ↔
      ZFSet.IsOrdinal top.val ∧ ∀ x : RankDomain (Order.succ alpha),
        ZFSet.IsOrdinal x.val → x.val ∈ top.val ∨ x = top := by
    simp [largestOrdinalFormula, RankPredicateFormula.realize_and, RankPredicateFormula.Realize,
      RankPredicateFormula.realize_or, rankFormulaOrdinal_realize]
  rw [semantics]
  constructor
  · rintro ⟨_, h⟩
    rcases h (ordinalDomainElement (endpoint alpha)) (ZFSet.isOrdinal_toZFSet alpha) with hm | he
    · have hr := ZFSet.rank_lt_of_mem hm
      have bound := Order.lt_succ_iff.mp top.property
      simp only [ordinalDomainElement, endpoint, Ordinal.rank_toZFSet] at hr
      exact False.elim ((not_lt_of_ge bound) hr)
    · exact (congrArg Subtype.val he).symm
  · intro same
    refine ⟨same ▸ ZFSet.isOrdinal_toZFSet alpha, ?_⟩
    intro x hx
    have bound := Order.lt_succ_iff.mp x.property
    rcases bound.lt_or_eq with hl | he
    · left
      rw [same, ← hx.toZFSet_rank_eq]
      exact Ordinal.toZFSet_mem_toZFSet_iff.mpr hl
    · right
      apply Subtype.ext
      rw [same]
      exact hx.toZFSet_rank_eq.symm.trans (congrArg Ordinal.toZFSet he)

theorem boundedMap_endpoint {alpha beta : Ordinal.{u}} (k : BoundedMap alpha beta) :
    ordinalAction k (endpoint alpha) = endpoint beta := by
  have h := rankMap_predicate k largestOrdinalFormula ![ordinalDomainElement (endpoint alpha)]
  have same : k ∘ ![ordinalDomainElement (endpoint alpha)] =
      ![k (ordinalDomainElement (endpoint alpha))] := by funext i; fin_cases i; rfl
  rw [same, largestOrdinalFormula_realize, largestOrdinalFormula_realize] at h
  apply Subtype.ext
  change (k (ordinalDomainElement (endpoint alpha))).val.rank = beta
  rw [h.mpr rfl, Ordinal.rank_toZFSet]

theorem boundedMap_hierarchy {alpha beta : Ordinal.{u}} (ha : Order.IsSuccLimit alpha)
    (k : BoundedMap alpha beta) (eta : OrdinalDomain (Order.succ alpha)) :
    k (rankHierarchy eta) = rankHierarchy (ordinalAction k eta) := by
  have he := Order.lt_succ_iff.mp eta.property
  rcases he.lt_or_eq with lower | same
  · exact rankMap_hierarchy_below ha (Order.le_succ alpha) k ⟨eta.val, lower⟩
  · have hsame : eta = endpoint alpha := Subtype.ext same
    rw [hsame, boundedMap_endpoint]
    exact boundedMap_top k

end IBLP
