import IBLP.Model.InaccessibleFormula
import IBLP.Model.RankBridge
import FullMarkedBLP.RankGraphClosure

namespace IBLP
open FullMarkedBLP
universe u

/-- A sharper bound than the usual finite-overhead estimate: if both sets
have rank at most a limit, each pair has smaller rank and the whole graph has
rank at most that limit. This includes graphs whose range is the endpoint. -/
theorem graph_rank_le_limit {alpha : Ordinal.{u}} (limit : Order.IsSuccLimit alpha)
    {x y f : ZFSet.{u}} (hx : x.rank ≤ alpha) (hy : y.rank ≤ alpha)
    (graph : f ⊆ ZFSet.prod x y) : f.rank ≤ alpha := by
  apply ZFSet.rank_le_iff.mpr
  intro p hp
  obtain ⟨a, ha, b, hb, rfl⟩ := ZFSet.mem_prod.mp (graph hp)
  have arank := (ZFSet.rank_lt_of_mem ha).trans_le hx
  have brank := (ZFSet.rank_lt_of_mem hb).trans_le hy
  simp only [ZFSet.pair, ZFSet.rank_pair, ZFSet.rank_singleton]
  exact max_lt (limit.succ_lt (limit.succ_lt arank))
    (limit.succ_lt (max_lt (limit.succ_lt arank) (limit.succ_lt brank)))

namespace TransitiveClass

def inaccessibleRankInclude (M : TransitiveClass.{u}) {lambda : Ordinal.{u}}
    (x : M.RankElement lambda) : M.Element := ⟨x.val, x.property.1⟩

/-- Internal powersets remain internal when comparing a rank cut with M.
Any candidate subset of x has rank at most rank(x), so no candidate is lost. -/
theorem internalPowerset_rankPart_iff (M : TransitiveClass.{u}) {lambda : Ordinal.{u}}
    (p x : M.RankElement lambda) :
    (M.rankPart lambda).InternalPowerset p x ↔
      M.InternalPowerset (M.inaccessibleRankInclude p) (M.inaccessibleRankInclude x) := by
  constructor
  · intro h z
    constructor
    · intro hz
      let z' : M.RankElement lambda :=
        ⟨z.val, z.property, (ZFSet.rank_lt_of_mem hz).trans p.property.2⟩
      exact (h z').mp hz
    · intro hz
      let z' : M.RankElement lambda :=
        ⟨z.val, z.property, (ZFSet.rank_mono hz).trans_lt x.property.2⟩
      exact (h z').mpr hz
  · intro h z
    exact h (M.inaccessibleRankInclude z)

theorem InternalPowerset.rank_le {M : TransitiveClass.{u}} {p x : M.Element}
    (h : M.InternalPowerset p x) : p.val.rank ≤ Order.succ x.val.rank := by
  have sub : p.val ⊆ ZFSet.powerset x.val := by
    intro z hz
    exact ZFSet.mem_powerset.mpr ((h (M.member p z hz)).mp hz)
  simpa only [ZFSet.rank_powerset] using ZFSet.rank_mono sub

/-- All possible counterexample graphs fit in the cut. Their membership in M
is retained; no environment function graph is substituted for an internal one. -/
theorem internalInitial_rankPart_iff (M : TransitiveClass.{u}) {lambda : Ordinal.{u}}
    (limit : Order.IsSuccLimit lambda) (k : M.RankElement lambda) :
    (M.rankPart lambda).InternalInitial k ↔ M.InternalInitial (M.inaccessibleRankInclude k) := by
  constructor
  · rintro ⟨ordinal, h⟩
    refine ⟨ordinal, ?_⟩
    intro a ha f hf
    have arank := (ZFSet.rank_lt_of_mem ha).trans k.property.2
    let a' : M.RankElement lambda := ⟨a.val, a.property, arank⟩
    let f' : M.RankElement lambda :=
      ⟨f.val, f.property, rank_function_lt_of_limit limit arank k.property.2 hf.1⟩
    exact h a' ha f' hf
  · rintro ⟨ordinal, h⟩
    refine ⟨ordinal, ?_⟩
    intro a ha f hf
    exact h (M.inaccessibleRankInclude a) ha (M.inaccessibleRankInclude f) hf

theorem noSmallCofinal_rankPart_iff (M : TransitiveClass.{u}) {lambda : Ordinal.{u}}
    (limit : Order.IsSuccLimit lambda) (k : M.RankElement lambda) :
    (M.rankPart lambda).NoSmallCofinal k ↔ M.NoSmallCofinal (M.inaccessibleRankInclude k) := by
  constructor
  · intro h a ha f hf
    have arank := (ZFSet.rank_lt_of_mem ha).trans k.property.2
    let a' : M.RankElement lambda := ⟨a.val, a.property, arank⟩
    let f' : M.RankElement lambda :=
      ⟨f.val, f.property, rank_function_lt_of_limit limit arank k.property.2 hf.1⟩
    exact h a' ha f' hf
  · intro h a ha f hf
    exact h (M.inaccessibleRankInclude a) ha (M.inaccessibleRankInclude f) hf

theorem internalRegular_rankPart_iff (M : TransitiveClass.{u}) {lambda : Ordinal.{u}}
    (limit : Order.IsSuccLimit lambda) (k : M.RankElement lambda) :
    (M.rankPart lambda).InternalRegular k ↔ M.InternalRegular (M.inaccessibleRankInclude k) := by
  exact and_congr (M.internalInitial_rankPart_iff limit k) (M.noSmallCofinal_rankPart_iff limit k)

theorem internalStrongLimit_rankPart_iff (M : TransitiveClass.{u}) {lambda : Ordinal.{u}}
    (limit : Order.IsSuccLimit lambda) (k : M.RankElement lambda) :
    (M.rankPart lambda).InternalStrongLimit k ↔ M.InternalStrongLimit (M.inaccessibleRankInclude k) := by
  constructor
  · intro h a ha p hp f hf
    have arank := (ZFSet.rank_lt_of_mem ha).trans k.property.2
    have prank := hp.rank_le.trans_lt (limit.succ_lt arank)
    let a' : M.RankElement lambda := ⟨a.val, a.property, arank⟩
    let p' : M.RankElement lambda := ⟨p.val, p.property, prank⟩
    let f' : M.RankElement lambda :=
      ⟨f.val, f.property, rank_function_lt_of_limit limit prank k.property.2 hf.1⟩
    exact h a' ha p' ((M.internalPowerset_rankPart_iff p' a').mpr hp) f' hf
  · intro h a ha p hp f hf
    exact h (M.inaccessibleRankInclude a) ha (M.inaccessibleRankInclude p)
      ((M.internalPowerset_rankPart_iff p a).mp hp) (M.inaccessibleRankInclude f) hf

theorem internalUncountable_rankPart_iff (M : TransitiveClass.{u}) {lambda : Ordinal.{u}}
    (k : M.RankElement lambda) :
    (M.rankPart lambda).InternalUncountable k ↔ M.InternalUncountable (M.inaccessibleRankInclude k) := by
  constructor
  · rintro ⟨w, ho, hf, hm⟩
    exact ⟨M.inaccessibleRankInclude w, ho, hf, hm⟩
  · rintro ⟨w, ho, hf, hm⟩
    exact ⟨⟨w.val, w.property, (ZFSet.rank_lt_of_mem hm).trans k.property.2⟩, ho, hf, hm⟩

theorem internalInaccessible_rankPart_iff (M : TransitiveClass.{u}) {lambda : Ordinal.{u}}
    (limit : Order.IsSuccLimit lambda) (k : M.RankElement lambda) :
    (M.rankPart lambda).InternalInaccessible k ↔
      M.InternalInaccessible (M.inaccessibleRankInclude k) := by
  exact and_congr (M.internalInitial_rankPart_iff limit k)
    (and_congr (M.internalUncountable_rankPart_iff k)
      (and_congr (M.noSmallCofinal_rankPart_iff limit k) (M.internalStrongLimit_rankPart_iff limit k)))

/-- Internal inaccessibility of points strictly below sufficiently high limit
cuts is preserved by actual elementary embeddings of those cuts. -/
theorem rankMap_internalInaccessible_iff {M N : TransitiveClass.{u}}
    {lambda mu : Ordinal.{u}} (sourceLimit : Order.IsSuccLimit lambda)
    (targetLimit : Order.IsSuccLimit mu)
    (j : (M.rankPart lambda).ElementaryMap (N.rankPart mu)) (k : M.RankElement lambda) :
    N.InternalInaccessible (N.inaccessibleRankInclude (j k)) ↔
      M.InternalInaccessible (M.inaccessibleRankInclude k) := by
  rw [← N.internalInaccessible_rankPart_iff targetLimit,
    ← M.internalInaccessible_rankPart_iff sourceLimit]
  exact j.internalInaccessible_iff k

/-- A limit strictly above the tested point supplies all witness ranks, even
when the ambient rank cut is itself a successor rank. The cutoff is not the
point whose inaccessibility is being tested. -/
theorem internalInaccessible_rankPart_below_iff (M : TransitiveClass.{u})
    {lambda cutoff : Ordinal.{u}} (limit : Order.IsSuccLimit cutoff) (included : cutoff ≤ lambda)
    (k : M.RankElement lambda) (below : k.val.rank < cutoff) :
    (M.rankPart lambda).InternalInaccessible k ↔
      M.InternalInaccessible (M.inaccessibleRankInclude k) := by
  have memberRank (a : M.Element) (ha : a.val ∈ k.val) : a.val.rank < cutoff :=
    (ZFSet.rank_lt_of_mem ha).trans below
  constructor
  · rintro ⟨initial, uncountable, regular, strong⟩
    refine ⟨⟨initial.1, ?_⟩, (M.internalUncountable_rankPart_iff k).mp uncountable, ?_, ?_⟩
    · intro a ha f hf
      let a' : M.RankElement lambda := ⟨a.val, a.property, (memberRank a ha).trans_le included⟩
      let f' : M.RankElement lambda := ⟨f.val, f.property,
        (rank_function_lt_of_limit limit (memberRank a ha) below hf.1).trans_le included⟩
      exact initial.2 a' ha f' hf
    · intro a ha f hf
      let a' : M.RankElement lambda := ⟨a.val, a.property, (memberRank a ha).trans_le included⟩
      let f' : M.RankElement lambda := ⟨f.val, f.property,
        (rank_function_lt_of_limit limit (memberRank a ha) below hf.1).trans_le included⟩
      exact regular a' ha f' hf
    · intro a ha p hp f hf
      have prank := hp.rank_le.trans_lt (limit.succ_lt (memberRank a ha))
      let a' : M.RankElement lambda := ⟨a.val, a.property, (memberRank a ha).trans_le included⟩
      let p' : M.RankElement lambda := ⟨p.val, p.property, prank.trans_le included⟩
      let f' : M.RankElement lambda := ⟨f.val, f.property,
        (rank_function_lt_of_limit limit prank below hf.1).trans_le included⟩
      exact strong a' ha p' ((M.internalPowerset_rankPart_iff p' a').mpr hp) f' hf
  · rintro ⟨initial, uncountable, regular, strong⟩
    refine ⟨⟨initial.1, ?_⟩, (M.internalUncountable_rankPart_iff k).mpr uncountable, ?_, ?_⟩
    · intro a ha f hf
      exact initial.2 (M.inaccessibleRankInclude a) ha (M.inaccessibleRankInclude f) hf
    · intro a ha f hf
      exact regular (M.inaccessibleRankInclude a) ha (M.inaccessibleRankInclude f) hf
    · intro a ha p hp f hf
      exact strong (M.inaccessibleRankInclude a) ha (M.inaccessibleRankInclude p)
        ((M.internalPowerset_rankPart_iff p a).mp hp) (M.inaccessibleRankInclude f) hf

theorem internalInaccessible_succRank_iff (M : TransitiveClass.{u}) {alpha : Ordinal.{u}}
    (limit : Order.IsSuccLimit alpha) (k : M.RankElement (Order.succ alpha))
    (below : k.val.rank < alpha) :
    (M.rankPart (Order.succ alpha)).InternalInaccessible k ↔
      M.InternalInaccessible (M.inaccessibleRankInclude k) :=
  M.internalInaccessible_rankPart_below_iff limit (Order.le_succ alpha) k below

/-- Direct preservation for the successor-rank maps used by IBLP. Only points
strictly below both displayed endpoints are covered by this theorem. -/
theorem successorRankMap_internalInaccessible_iff {M N : TransitiveClass.{u}}
    {alpha beta : Ordinal.{u}} (sourceLimit : Order.IsSuccLimit alpha)
    (targetLimit : Order.IsSuccLimit beta)
    (j : (M.rankPart (Order.succ alpha)).ElementaryMap (N.rankPart (Order.succ beta)))
    (k : M.RankElement (Order.succ alpha))
    (sourceBelow : k.val.rank < alpha) (targetBelow : (j k).val.rank < beta) :
    N.InternalInaccessible (N.inaccessibleRankInclude (j k)) ↔
      M.InternalInaccessible (M.inaccessibleRankInclude k) := by
  rw [← N.internalInaccessible_succRank_iff targetLimit _ targetBelow,
    ← M.internalInaccessible_succRank_iff sourceLimit _ sourceBelow]
  exact j.internalInaccessible_iff k

/-- Endpoint absoluteness uses the sharp graph bound, not a finite-overhead
estimate beyond the endpoint. This is needed to transport a trace's source
inaccessibility to its actual final codomain. -/
theorem internalInaccessible_rankPart_endpoint_iff (M : TransitiveClass.{u})
    {alpha : Ordinal.{u}} (limit : Order.IsSuccLimit alpha)
    (k : M.RankElement (Order.succ alpha)) (bound : k.val.rank ≤ alpha) :
    (M.rankPart (Order.succ alpha)).InternalInaccessible k ↔
      M.InternalInaccessible (M.inaccessibleRankInclude k) := by
  have memberRank (a : M.Element) (ha : a.val ∈ k.val) : a.val.rank < alpha :=
    (ZFSet.rank_lt_of_mem ha).trans_le bound
  constructor
  · rintro ⟨initial, uncountable, regular, strong⟩
    refine ⟨⟨initial.1, ?_⟩, (M.internalUncountable_rankPart_iff k).mp uncountable, ?_, ?_⟩
    · intro a ha f hf
      let a' : M.RankElement (Order.succ alpha) :=
        ⟨a.val, a.property, (memberRank a ha).trans (Order.lt_succ alpha)⟩
      let f' : M.RankElement (Order.succ alpha) := ⟨f.val, f.property,
        (graph_rank_le_limit limit (memberRank a ha).le bound hf.1.1).trans_lt (Order.lt_succ alpha)⟩
      exact initial.2 a' ha f' hf
    · intro a ha f hf
      let a' : M.RankElement (Order.succ alpha) :=
        ⟨a.val, a.property, (memberRank a ha).trans (Order.lt_succ alpha)⟩
      let f' : M.RankElement (Order.succ alpha) := ⟨f.val, f.property,
        (graph_rank_le_limit limit (memberRank a ha).le bound hf.1.1).trans_lt (Order.lt_succ alpha)⟩
      exact regular a' ha f' hf
    · intro a ha p hp f hf
      have prank := hp.rank_le.trans_lt (limit.succ_lt (memberRank a ha))
      let a' : M.RankElement (Order.succ alpha) :=
        ⟨a.val, a.property, (memberRank a ha).trans (Order.lt_succ alpha)⟩
      let p' : M.RankElement (Order.succ alpha) :=
        ⟨p.val, p.property, prank.trans (Order.lt_succ alpha)⟩
      let f' : M.RankElement (Order.succ alpha) := ⟨f.val, f.property,
        (graph_rank_le_limit limit prank.le bound hf.1.1).trans_lt (Order.lt_succ alpha)⟩
      exact strong a' ha p' ((M.internalPowerset_rankPart_iff p' a').mpr hp) f' hf
  · rintro ⟨initial, uncountable, regular, strong⟩
    refine ⟨⟨initial.1, ?_⟩, (M.internalUncountable_rankPart_iff k).mpr uncountable, ?_, ?_⟩
    · intro a ha f hf
      exact initial.2 (M.inaccessibleRankInclude a) ha (M.inaccessibleRankInclude f) hf
    · intro a ha f hf
      exact regular (M.inaccessibleRankInclude a) ha (M.inaccessibleRankInclude f) hf
    · intro a ha p hp f hf
      exact strong (M.inaccessibleRankInclude a) ha (M.inaccessibleRankInclude p)
        ((M.internalPowerset_rankPart_iff p a).mp hp) (M.inaccessibleRankInclude f) hf

end TransitiveClass
end IBLP
