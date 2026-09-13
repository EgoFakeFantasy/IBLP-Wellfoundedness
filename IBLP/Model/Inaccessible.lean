import IBLP.Model.InaccessibleAbsolute

namespace IBLP
open FullMarkedBLP
universe u

theorem setNonzeroLimit_ordinal_iff (a : Ordinal.{u}) :
    setNonzeroLimit a.toZFSet ↔ Order.IsSuccLimit a := by
  constructor
  · rintro ⟨⟨z, hz⟩, cofinal⟩
    rw [Ordinal.isSuccLimit_iff, Order.isSuccPrelimit_iff_succ_lt]
    refine ⟨?_, ?_⟩
    · intro zero
      have bound : z.rank < a := by
        simpa only [Ordinal.rank_toZFSet] using ZFSet.rank_lt_of_mem hz
      rw [zero] at bound
      exact (not_lt_of_ge zero_le) bound
    · intro b hb
      obtain ⟨w, hw, above⟩ := cofinal b.toZFSet (Ordinal.toZFSet_mem_toZFSet_iff.mpr hb)
      have lower : b < w.rank := by
        simpa only [Ordinal.rank_toZFSet] using ZFSet.rank_lt_of_mem above
      have upper : w.rank < a := by
        simpa only [Ordinal.rank_toZFSet] using ZFSet.rank_lt_of_mem hw
      exact (Order.succ_le_of_lt lower).trans_lt upper
  · intro limit
    refine ⟨⟨(0 : Ordinal.{u}).toZFSet, Ordinal.toZFSet_mem_toZFSet_iff.mpr limit.pos⟩, ?_⟩
    intro z hz
    obtain ⟨b, hb, rep⟩ := Ordinal.mem_toZFSet_iff.mp hz
    refine ⟨(Order.succ b).toZFSet, Ordinal.toZFSet_mem_toZFSet_iff.mpr (limit.succ_lt hb), ?_⟩
    rw [← rep]
    exact Ordinal.toZFSet_mem_toZFSet_iff.mpr (Order.lt_succ b)

theorem setFirstLimit_omega : setFirstLimit Ordinal.omega0.toZFSet := by
  refine ⟨(setNonzeroLimit_ordinal_iff _).mpr Ordinal.isSuccLimit_omega0, ?_⟩
  intro z hz hlimit
  obtain ⟨b, below, rep⟩ := Ordinal.mem_toZFSet_iff.mp hz
  rw [← rep] at hlimit
  exact (not_lt_of_ge (Ordinal.omega0_le_of_isSuccLimit
    ((setNonzeroLimit_ordinal_iff _).mp hlimit))) below

theorem setFirstLimit_ordinal_iff {x : ZFSet.{u}} (ordinal : ZFSet.IsOrdinal x) :
    setFirstLimit x ↔ x = Ordinal.omega0.toZFSet := by
  constructor
  · intro first
    have rep := ordinal.toZFSet_rank_eq
    have limit := (setNonzeroLimit_ordinal_iff x.rank).mp (by rw [rep]; exact first.1)
    have lower := Ordinal.omega0_le_of_isSuccLimit limit
    have upper : x.rank ≤ Ordinal.omega0 := by
      by_contra h
      have member : Ordinal.omega0.toZFSet ∈ x := by
        rw [← rep]
        exact Ordinal.toZFSet_mem_toZFSet_iff.mpr (lt_of_not_ge h)
      exact first.2 _ member setFirstLimit_omega.1
    have same := le_antisymm upper lower
    rw [← rep, same]
  · rintro rfl
    exact setFirstLimit_omega

theorem TransitiveClass.internalUncountable_iff (M : TransitiveClass.{u})
    (k : M.Element) : M.InternalUncountable k ↔ Ordinal.omega0.toZFSet ∈ k.val := by
  constructor
  · rintro ⟨w, ordinal, first, member⟩
    rwa [(setFirstLimit_ordinal_iff ordinal).mp first] at member
  · intro member
    exact ⟨M.member k _ member, ZFSet.isOrdinal_toZFSet _, setFirstLimit_omega, member⟩

theorem TransitiveClass.internalUncountable_ordinal_iff (M : TransitiveClass.{u})
    (k : M.Element) (ordinal : ZFSet.IsOrdinal k.val) :
    M.InternalUncountable k ↔ Ordinal.omega0 < k.val.rank := by
  rw [M.internalUncountable_iff, ← ordinal.toZFSet_rank_eq,
    Ordinal.toZFSet_mem_toZFSet_iff]
  rw [Ordinal.rank_toZFSet]

end IBLP
