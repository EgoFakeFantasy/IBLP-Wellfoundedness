import IBLP.Rank.WeakTruncation

namespace IBLP

universe u v

/-- 内部模型也可使用的截断空间。每个实例必须证明这些集合与秩性质。 -/
structure CutSpace (S : Type v) where
  rank : S → Ordinal.{u}
  mem : S → S → Prop
  cut : Ordinal.{u} → S → S
  mem_cut : ∀ x z eta, mem x (cut eta z) ↔ mem x z ∧ rank x < eta
  rank_mem_lt : ∀ {x z}, mem x z → rank x < rank z
  cut_rank_le : ∀ eta z, rank (cut eta z) ≤ eta
  ext : ∀ {x y}, (∀ z, mem z x ↔ mem z y) → x = y

namespace CutSpace

variable {S : Type v} (C : CutSpace.{u} S)

theorem cut_cut (alpha beta : Ordinal.{u}) (z : S) :
    C.cut alpha (C.cut beta z) = C.cut (min alpha beta) z := by
  apply C.ext
  intro x
  simp only [C.mem_cut, lt_min_iff]
  tauto

theorem cut_eq_self {eta : Ordinal.{u}} {z : S} (h : C.rank z ≤ eta) : C.cut eta z = z := by
  apply C.ext
  intro x
  rw [C.mem_cut]
  exact ⟨And.left, fun hm => ⟨hm, (C.rank_mem_lt hm).trans_le h⟩⟩

theorem cut_lower {alpha beta : Ordinal.{u}} (h : alpha ≤ beta) (z : S) :
    C.cut alpha (C.cut beta z) = C.cut alpha z := by rw [C.cut_cut, min_eq_left h]

end CutSpace

/-- 环境集合的实例；未来内部模型实例沿用同一套有限词定理。 -/
noncomputable def zfCutSpace : CutSpace.{u} ZFSet.{u} where
  rank := ZFSet.rank
  mem := (· ∈ ·)
  cut := fun eta z => (truncate eta z).val
  mem_cut := fun _ _ _ => by simp only [truncate, ZFSet.mem_inter, ZFSet.mem_vonNeumann]
  rank_mem_lt := ZFSet.rank_lt_of_mem
  cut_rank_le := truncate_rank_le
  ext := ZFSet.ext

end IBLP
