import IBLP.Rank.Between

namespace IBLP
open FullMarkedBLP

universe u

/-- 给定序偶本身已经属于秩结构，就不需极限秩来保证其中的单点集存在。 -/
theorem orderedPair_absolute {lambda : Ordinal.{u}} (z x y : RankDomain lambda) :
    rankIsOrderedPair z x y ↔ z.val = ZFSet.pair x.val y.val := by
  constructor
  · rintro ⟨s, t, hs, ht, hz⟩
    rw [rankIsUnorderedPair_iff] at hs ht hz
    rw [hz, hs, ht]
    simp [ZFSet.pair]
  · intro hz
    have hs : ({x.val, x.val} : ZFSet.{u}) ∈ z.val := by rw [hz]; simp [ZFSet.pair]
    have ht : ({x.val, y.val} : ZFSet.{u}) ∈ z.val := by rw [hz]; simp [ZFSet.pair]
    refine ⟨rankMember z _ hs, rankMember z _ ht, ?_, ?_, ?_⟩
    · exact (rankIsUnorderedPair_iff _ _ _).mpr rfl
    · exact (rankIsUnorderedPair_iff _ _ _).mpr rfl
    · apply (rankIsUnorderedPair_iff _ _ _).mpr
      simpa [ZFSet.pair, rankMember] using hz

theorem graphApplies_absolute {lambda : Ordinal.{u}} (f x y : RankDomain lambda) :
    rankGraphApplies f x y ↔ ZFSet.pair x.val y.val ∈ f.val := by
  constructor
  · rintro ⟨p, hp, he⟩
    rwa [(orderedPair_absolute _ _ _).mp he] at hp
  · intro hp
    exact ⟨rankMember f _ hp, hp, (orderedPair_absolute _ _ _).mpr rfl⟩

theorem graphBetween_absolute {lambda : Ordinal.{u}} (f x y : RankDomain lambda) :
    rankGraphBetween f x y ↔ f.val ⊆ ZFSet.prod x.val y.val := by
  constructor
  · intro h p hp
    obtain ⟨a, b, ha, hb, he⟩ := h (rankMember f p hp) hp
    exact ZFSet.mem_prod.mpr ⟨a.val, ha, b.val, hb, (orderedPair_absolute _ _ _).mp he⟩
  · intro h p hp
    obtain ⟨a, ha, b, hb, he⟩ := ZFSet.mem_prod.mp (h hp)
    exact ⟨rankMember x a ha, rankMember y b hb, ha, hb, (orderedPair_absolute _ _ _).mpr he⟩

theorem function_absolute {lambda : Ordinal.{u}} (f x y : RankDomain lambda) :
    rankIsFunction f x y ↔ ZFSet.IsFunc x.val y.val f.val := by
  constructor
  · rintro ⟨hg, ht⟩
    have hg' := (graphBetween_absolute f x y).mp hg
    refine ⟨hg', ?_⟩
    intro a ha
    obtain ⟨b, hb, hab, hu⟩ := ht (rankMember x a ha) ha
    refine ⟨b.val, (graphApplies_absolute _ _ _).mp hab, ?_⟩
    intro c hc
    have hcy := (ZFSet.pair_mem_prod.mp (hg' hc)).2
    exact congrArg Subtype.val (hu (rankMember y c hcy) ((graphApplies_absolute _ _ _).mpr hc))
  · rintro ⟨hg, ht⟩
    refine ⟨(graphBetween_absolute f x y).mpr hg, ?_⟩
    intro a ha
    obtain ⟨b, hb, hu⟩ := ht a.val ha
    have hby := (ZFSet.pair_mem_prod.mp (hg hb)).2
    refine ⟨rankMember y b hby, hby, (graphApplies_absolute _ _ _).mpr hb, ?_⟩
    intro c hc
    exact Subtype.ext (hu c.val ((graphApplies_absolute _ _ _).mp hc))

theorem rankMap_graphApplies_iff {lambda mu : Ordinal.{u}} (j : RankMap lambda mu)
    (f x y : RankDomain lambda) : rankGraphApplies (j f) (j x) (j y) ↔ rankGraphApplies f x y := by
  have h := j.map_formula rankGraphAppliesFormula ![f, x, y]
  have he : j ∘ ![f, x, y] = ![j f, j x, j y] := by funext i; fin_cases i <;> rfl
  rw [he, rankGraphAppliesFormula_realize, rankGraphAppliesFormula_realize] at h
  exact h

end IBLP
