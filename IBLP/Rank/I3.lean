import FullMarkedBLP.RankCriticalSequenceInaccessible

namespace IBLP
open FullMarkedBLP

universe u

/-- 本文的 I3：某个极限秩上的非平凡、全一阶初等自嵌入。 -/
def I3 : Prop :=
  ∃ (lambda : Ordinal.{u}) (_ : Order.IsSuccLimit lambda)
    (j : RankElementaryEmbedding lambda), ∃ x, j x ≠ x

/-- 由固定全部序数推出固定全部集合；没有额外的秩刚性假设。 -/
theorem rankEmbedding_fixes_all_of_fixes_ordinals {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) (j : RankElementaryEmbedding lambda)
    (fixed : ∀ o, rankOrdinalAction j o = o) : ∀ x, j x = x := by
  have all : ∀ alpha : Ordinal.{u}, ∀ z : RankDomain lambda,
      z.val.rank = alpha → j z = z := by
    intro alpha
    apply (wellFounded_lt : WellFounded ((· < ·) : Ordinal.{u} → Ordinal.{u} → Prop)).induction alpha
    intro level ih z hz
    have imageRank : (j z).val.rank = z.val.rank :=
      (rankElementary_rank hl j z).trans (congrArg Subtype.val (fixed _))
    apply Subtype.ext
    apply ZFSet.ext
    intro w
    constructor
    · intro hw
      have smaller : w.rank < level := (ZFSet.rank_lt_of_mem hw).trans_eq (imageRank.trans hz)
      let w' := rankMember (j z) w hw
      have hwf : j w' = w' := ih w.rank smaller w' rfl
      have inside : (j w').val ∈ (j z).val := by rw [hwf]; exact hw
      exact (rankElementary_mem_iff j w' z).mp inside
    · intro hw
      have smaller : w.rank < level := (ZFSet.rank_lt_of_mem hw).trans_eq hz
      let w' := rankMember z w hw
      have hwf : j w' = w' := ih w.rank smaller w' rfl
      have inside := (rankElementary_mem_iff j w' z).mpr hw
      rw [hwf] at inside
      exact inside
  exact fun x => all x.val.rank x rfl

theorem exists_criticalPoint_of_nontrivial {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) (j : RankElementaryEmbedding lambda)
    (nontrivial : ∃ x, j x ≠ x) : ∃ c, RankCriticalPoint j c := by
  apply rankCriticalPoint_exists j
  by_contra hn
  have fixed : ∀ o, rankOrdinalAction j o = o := by simpa using hn
  obtain ⟨x, hx⟩ := nontrivial
  exact hx (rankEmbedding_fixes_all_of_fixes_ordinals hl j fixed x)

/-- 将原非平凡性转为临界点数据，而非加强 I3 的定义。 -/
theorem i3_iff_criticalPoint : I3.{u} ↔
    ∃ (lambda : Ordinal.{u}) (_ : Order.IsSuccLimit lambda)
      (j : RankElementaryEmbedding lambda) (c : OrdinalDomain lambda), RankCriticalPoint j c := by
  constructor
  · rintro ⟨lambda, hl, j, h⟩
    obtain ⟨c, hc⟩ := exists_criticalPoint_of_nontrivial hl j h
    exact ⟨lambda, hl, j, c, hc⟩
  · rintro ⟨lambda, hl, j, c, hc⟩
    refine ⟨lambda, hl, j, ordinalDomainElement c, ?_⟩
    intro h
    apply hc.1
    apply Subtype.ext
    change (j (ordinalDomainElement c)).val.rank = c.val
    rw [h]
    exact Ordinal.rank_toZFSet c.val

/-- 普通函数合成幂；不与 application 幂混用。 -/
noncomputable def embeddingPower {lambda : Ordinal.{u}}
    (j : RankElementaryEmbedding lambda) : Nat → RankElementaryEmbedding lambda
  | 0 => FirstOrder.Language.ElementaryEmbedding.refl membershipLanguage (RankDomain lambda)
  | n + 1 => j.comp (embeddingPower j n)

theorem embeddingPower_ordinal_zero {lambda : Ordinal.{u}}
    (j : RankElementaryEmbedding lambda) (o : OrdinalDomain lambda) :
    rankOrdinalAction (embeddingPower j 0) o = o := by
  apply Subtype.ext
  exact Ordinal.rank_toZFSet o.val

theorem embeddingPower_on_sequence {lambda : Ordinal.{u}}
    (j : RankElementaryEmbedding lambda) (c : OrdinalDomain lambda) (s i : Nat) :
    rankOrdinalAction (embeddingPower j s) (rankCriticalSequence j c i) =
      rankCriticalSequence j c (i + s) := by
  induction s with
  | zero => simpa using embeddingPower_ordinal_zero j (rankCriticalSequence j c i)
  | succ s ih =>
    change rankOrdinalAction (j.comp (embeddingPower j s)) _ = _
    rw [rankOrdinalAction_comp, ih]
    rfl

/-- 主稿第9节的 g_s=(j^s)^+(j)。 -/
noncomputable def shiftEmbedding {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) (j : RankElementaryEmbedding lambda) (s : Nat) :
    RankElementaryEmbedding lambda := rankApply hl (embeddingPower j s) j

theorem shiftEmbedding_criticalPoint {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {j : RankElementaryEmbedding lambda}
    {c : OrdinalDomain lambda} (hc : RankCriticalPoint j c) (s : Nat) :
    RankCriticalPoint (shiftEmbedding hl j s) (rankCriticalSequence j c s) := by
  have h := rankApply_criticalPoint hl (embeddingPower j s) hc
  have hseq : rankOrdinalAction (embeddingPower j s) c = rankCriticalSequence j c s := by
    simpa only [rankCriticalSequence, Nat.zero_add] using embeddingPower_on_sequence j c s 0
  rw [hseq] at h
  exact h

theorem shiftEmbedding_on_tail {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) (j : RankElementaryEmbedding lambda)
    (c : OrdinalDomain lambda) (s i : Nat) :
    rankOrdinalAction (shiftEmbedding hl j s) (rankCriticalSequence j c (i + s)) =
      rankCriticalSequence j c (i + s + 1) := by
  rw [← embeddingPower_on_sequence j c s i]
  unfold shiftEmbedding
  rw [rankApply_ordinal_image]
  change rankOrdinalAction (embeddingPower j s) (rankCriticalSequence j c (i + 1)) = _
  rw [embeddingPower_on_sequence]
  congr 1
  omega

end IBLP
