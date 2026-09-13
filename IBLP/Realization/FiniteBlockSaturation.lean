import IBLP.Realization.CopyBlockSaturation
import IBLP.Realization.CopyBlockLayout
import IBLP.Realization.FiniteCopiesRealized
import IBLP.CutGeometry

namespace IBLP.FiniteBoundedData
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (D : FiniteBoundedData stage a)

include D in
/-- The conditional saturation of the source tail survives every actual
finite full-tail copy. Intermediate global saturation is not required. -/
theorem rawCopies_tail_saturated (proper : IBLP.ProperMarks a)
    {last : IBLP.Row} {p m : Nat} {b : IBLP.Pattern}
    (hlast : a.getLast? = some last) (hp : last.p = some p)
    (run : IBLP.rawCopies m a = some b) (saturated : IBLP.BlockSaturated a p a.length) :
    IBLP.BlockSaturated b (p + m * (a.length - p)) (a.length + m * (a.length - p)) := by
  induction m generalizing stage a b last p with
  | zero =>
    have same : a = b := Option.some.inj run
    subst b
    simpa using saturated
  | succ m ih =>
    obtain ⟨middle, first, rest⟩ := Option.bind_eq_some_iff.mp run
    have atLast := IBLP.getLast_rowAt hlast
    have nonempty := IBLP.rowAt_pos atLast
    have pred : IBLP.predecessor a a.length = some p := by
      simp [IBLP.predecessor, atLast, hp]
    have pn := IBLP.predecessor_lt D.valid D.shapes pred
    have headBound : 0 < last.columns.length := by
      have := (D.valid _ _ atLast).2.1
      omega
    let minimum := last.columns[0]'headBound
    have hm : last.columns.head? = some minimum := by
      simp only [List.head?_eq_getElem?, List.getElem?_eq_getElem headBound, minimum]
    obtain ⟨next, hnext, copiedNext⟩ := IBLP.rawCopy_last first hlast hp
    have hpNext := (D.copied_control nonempty atLast hm hp copiedNext).1
    let nextData := D.rawCopyData nonempty proper first hlast hm hp
    have nextProper := (D.rawCopy_geometry proper first).2.2
    have nextSat := D.rawCopy_block_saturated proper first hlast hm hp saturated
    have result := ih nextData nextProper hnext hpNext rest nextSat
    have middleLength := IBLP.rawCopy_length first hlast hp
    have width : middle.length - a.length = a.length - p := by omega
    rw [width] at result
    have lower : a.length + m * (a.length - p) = p + (m + 1) * (a.length - p) := by
      rw [Nat.succ_mul]
      omega
    have upper : middle.length + m * (a.length - p) = a.length + (m + 1) * (a.length - p) := by
      rw [Nat.succ_mul]
      omega
    rwa [lower, upper] at result

end IBLP.FiniteBoundedData

namespace IBLP.BoundedRealization
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (R : BoundedRealization stage a)

include R in
/-- Manuscript (6.2) in any copied block, using the actual parent
saturation. Later raw copies preserve all rows consulted by this property. -/
theorem rawCopies_block_saturated {last : IBLP.Row} {p m k : Nat} {b : IBLP.Pattern}
    (hlast : a.getLast? = some last) (hp : last.p = some p)
    (run : IBLP.rawCopies m a = some b) (within : k < m) :
    IBLP.BlockSaturated b (a.length + k * (a.length - p))
      (a.length + (k + 1) * (a.length - p)) := by
  obtain ⟨middle, first, _, unchanged⟩ :=
    R.data.rawCopies_stage_prefix R.proper hlast hp run (Nat.succ_le_of_lt within)
  have saturated := R.data.rawCopies_tail_saturated R.proper hlast hp first (R.saturated.block p a.length)
  have pred : IBLP.predecessor a a.length = some p := by
    simp [IBLP.predecessor, IBLP.getLast_rowAt hlast, hp]
  have pn := IBLP.predecessor_lt R.data.valid R.data.shapes pred
  have lower : p + (k + 1) * (a.length - p) = a.length + k * (a.length - p) := by
    rw [Nat.succ_mul]
    omega
  rw [lower] at saturated
  obtain ⟨nextStage, _, S, _, _⟩ := R.toMarkedRealization.rawCopies_realization_exists (k + 1) first
  exact saturated.congr_prefix S.data.valid S.data.shapes unchanged

include R in
/-- The original cut preserves conditional saturation in every complete
copy block, including the final block's last retained carrier. -/
theorem copies_cut_block_saturated {last : IBLP.Row} {p m k : Nat} {b c : IBLP.Pattern}
    (hlast : a.getLast? = some last) (hp : last.p = some p)
    (run : IBLP.rawCopies m a = some b) (cut : IBLP.cut b = some c) (within : k < m) :
    IBLP.BlockSaturated c (a.length + k * (a.length - p))
      (a.length + (k + 1) * (a.length - p)) := by
  have saturated := R.rawCopies_block_saturated hlast hp run within
  obtain ⟨nextStage, _, S, _, _⟩ := R.toMarkedRealization.rawCopies_realization_exists m run
  have length := (R.data.rawCopies_length_control R.proper hlast hp run).1
  have mulBound : (k + 1) * (a.length - p) ≤ m * (a.length - p) :=
    Nat.mul_le_mul_right _ (Nat.succ_le_of_lt within)
  apply saturated.congr_prefix S.data.valid S.data.shapes
  intro i before
  rw [(IBLP.cut_decomposition cut).2, IBLP.rowAt_take (by omega : i ≤ b.length - 1)]

end IBLP.BoundedRealization
