import IBLP.Rank.GraphAbsoluteness

namespace IBLP
open FullMarkedBLP

universe u

def includeOrdinal {alpha lambda : Ordinal.{u}} (h : alpha ≤ lambda)
    (eta : OrdinalDomain alpha) : OrdinalDomain lambda := ⟨eta.val, eta.property.trans_le h⟩

/-- 小极限秩内构造的递归图，放到任意更大秩；环境秩可以是后继。 -/
noncomputable def hierarchyGraphIn {alpha lambda : Ordinal.{u}}
    (ha : Order.IsSuccLimit alpha) (h : alpha ≤ lambda) (upper : OrdinalDomain alpha) :
    RankDomain lambda := rankInclude h (rankHierarchyGraph ha upper)

theorem hierarchyGraphIn_function {alpha lambda : Ordinal.{u}}
    (ha : Order.IsSuccLimit alpha) (h : alpha ≤ lambda) (upper : OrdinalDomain alpha) :
    rankIsFunction (hierarchyGraphIn ha h upper) (ordinalDomainElement (includeOrdinal h upper))
      (rankHierarchy (includeOrdinal h upper)) :=
  (function_absolute _ _ _).mpr (zfFunctionGraph_isFunc (rankHierarchyMember upper))

theorem hierarchyGraphIn_applies_iff {alpha lambda : Ordinal.{u}}
    (ha : Order.IsSuccLimit alpha) (h : alpha ≤ lambda) (upper : OrdinalDomain alpha)
    (i value : RankDomain lambda) :
    rankGraphApplies (hierarchyGraphIn ha h upper) i value ↔
      i.val ∈ upper.val.toZFSet ∧ value.val = ZFSet.vonNeumann i.val.rank := by
  rw [graphApplies_absolute]
  change ZFSet.pair i.val value.val ∈ zfFunctionGraph (rankHierarchyMember upper) ↔ _
  rw [mem_zfFunctionGraph]
  constructor
  · rintro ⟨member, image⟩
    exact ⟨member, image.symm⟩
  · rintro ⟨member, image⟩
    exact ⟨member, image.symm⟩

theorem hierarchyGraphIn_at {alpha lambda : Ordinal.{u}}
    (ha : Order.IsSuccLimit alpha) (h : alpha ≤ lambda)
    {upper beta : OrdinalDomain alpha} (below : beta < upper) :
    rankGraphApplies (hierarchyGraphIn ha h upper) (ordinalDomainElement (includeOrdinal h beta))
      (rankHierarchy (includeOrdinal h beta)) := by
  apply (hierarchyGraphIn_applies_iff ha h upper _ _).mpr
  exact ⟨Ordinal.toZFSet_mem_toZFSet_iff.mpr below, by
    simp only [ordinalDomainElement, rankHierarchy, Ordinal.rank_toZFSet, includeOrdinal]⟩

theorem hierarchyGraphIn_recursion {alpha lambda : Ordinal.{u}}
    (ha : Order.IsSuccLimit alpha) (h : alpha ≤ lambda) (upper : OrdinalDomain alpha) :
    RankHierarchyRec (hierarchyGraphIn ha h upper) := by
  intro i value applies z
  obtain ⟨member, image⟩ := (hierarchyGraphIn_applies_iff ha h upper i value).mp applies
  obtain ⟨beta, below, representation⟩ := Ordinal.mem_toZFSet_iff.mp member
  let level : OrdinalDomain alpha := ⟨beta, below.trans upper.property⟩
  have same : ordinalDomainElement (includeOrdinal h level) = i := Subtype.ext representation
  subst i
  simp only [ordinalDomainElement, includeOrdinal, Ordinal.rank_toZFSet] at image
  rw [image]
  constructor
  · intro hz
    obtain ⟨gamma, less, subset⟩ := ZFSet.mem_vonNeumann'.mp hz
    let lower : OrdinalDomain alpha := ⟨gamma, less.trans level.property⟩
    refine ⟨ordinalDomainElement (includeOrdinal h lower), rankHierarchy (includeOrdinal h lower),
      Ordinal.toZFSet_mem_toZFSet_iff.mpr less, hierarchyGraphIn_at ha h (less.trans below), ?_⟩
    intro w hw
    exact subset hw
  · rintro ⟨a, b, smaller, edge, subset⟩
    have bound := ZFSet.rank_lt_of_mem smaller
    have less : a.val.rank < beta := by
      simpa only [ordinalDomainElement, includeOrdinal, Ordinal.rank_toZFSet] using bound
    have valueEq := ((hierarchyGraphIn_applies_iff ha h upper a b).mp edge).2
    apply ZFSet.mem_vonNeumann'.mpr
    refine ⟨a.val.rank, less, ?_⟩
    intro w hw
    rw [← valueEq]
    exact subset (rankMember z w hw) hw

theorem rankMap_hierarchy_below {alpha lambda mu : Ordinal.{u}}
    (ha : Order.IsSuccLimit alpha) (h : alpha ≤ lambda) (j : RankMap lambda mu)
    (eta : OrdinalDomain alpha) :
    j (rankHierarchy (includeOrdinal h eta)) =
      rankHierarchy (ordinalAction j (includeOrdinal h eta)) := by
  let upper : OrdinalDomain alpha := ⟨Order.succ eta.val, ha.succ_lt eta.property⟩
  have below : eta < upper := Order.lt_succ eta.val
  let graph := hierarchyGraphIn ha h upper
  have function := (rankMap_function_iff j _ _ _).mpr (hierarchyGraphIn_function ha h upper)
  have ordinal := (rankMap_isOrdinal_iff j (ordinalDomainElement (includeOrdinal h upper))).mpr
    (ZFSet.isOrdinal_toZFSet upper.val)
  have recursion := (rankMap_hierarchyRec_iff j graph).mpr (hierarchyGraphIn_recursion ha h upper)
  have edge := (rankMap_graphApplies_iff j _ _ _).mpr (hierarchyGraphIn_at ha h below)
  have member := (rankMap_mem_iff j (ordinalDomainElement (includeOrdinal h eta))
    (ordinalDomainElement (includeOrdinal h upper))).mpr (Ordinal.toZFSet_mem_toZFSet_iff.mpr below)
  rw [← ordinalAction_element j (includeOrdinal h eta)] at edge member
  exact rankHierarchyRec_unique function ordinal recursion _ _ member edge

end IBLP
