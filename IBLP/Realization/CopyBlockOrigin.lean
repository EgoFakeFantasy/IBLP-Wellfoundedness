import IBLP.Realization.CopyBlockLayout
import IBLP.CutGeometry

namespace IBLP.FiniteBoundedData
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (D : FiniteBoundedData stage a)

include D in
/-- Each row in the k-th new block is the actual copy of the row one fixed
block width below it, at the recovered k-copy stage. The later copies do not
change this row. The last control row is outside these half-open blocks. -/
theorem rawCopies_block_origin (proper : IBLP.ProperMarks a)
    {last : IBLP.Row} {p m k i : Nat} {b : IBLP.Pattern}
    (hlast : a.getLast? = some last) (hp : last.p = some p)
    (run : IBLP.rawCopies m a = some b) (within : k < m)
    (lower : a.length + k * (a.length - p) ≤ i)
    (upper : i < a.length + (k + 1) * (a.length - p)) :
    ∃ before control copied,
      IBLP.rawCopies k a = some before ∧
      before.length = a.length + k * (a.length - p) ∧
      before.getLast? = some control ∧
      control.p = some (p + k * (a.length - p)) ∧
      p + k * (a.length - p) ≤ i - (a.length - p) ∧
      i - (a.length - p) < before.length ∧
      IBLP.copyRow before control (i - (a.length - p)) = some copied ∧
      IBLP.rowAt b i = some copied := by
  obtain ⟨before, first, rest⟩ := IBLP.rawCopies_split run within.le
  obtain ⟨length, control, atControl, controlP⟩ := D.rawCopies_length_control proper hlast hp first
  have remaining : m - k = (m - k - 1) + 1 := by omega
  rw [remaining] at rest
  obtain ⟨after, copy, later⟩ := Option.bind_eq_some_iff.mp rest
  have pred : IBLP.predecessor a a.length = some p := by
    simp [IBLP.predecessor, IBLP.getLast_rowAt hlast, hp]
  have pn := IBLP.predecessor_lt D.valid D.shapes pred
  have width : before.length - (p + k * (a.length - p)) = a.length - p := by omega
  have afterLength := IBLP.rawCopy_length copy atControl controlP
  rw [width] at afterLength
  have expanded : (k + 1) * (a.length - p) = k * (a.length - p) + (a.length - p) := by
    exact Nat.succ_mul k (a.length - p)
  rw [expanded] at upper
  have positive : 0 < i := by omega
  have included : i < after.length := by omega
  obtain ⟨copied, atCopied⟩ := IBLP.rowAt_exists positive included.le
  obtain ⟨source, sourceLower, sourceUpper, owner, rowCopy⟩ :=
    IBLP.rawCopy_row_origin copy atControl controlP (by omega) atCopied
  rw [width] at owner
  have same : source = i - (a.length - p) := by omega
  subst source
  exact ⟨before, control, copied, first, length, atControl, controlP,
    sourceLower, by omega, rowCopy, (IBLP.rawCopies_prefix later included).trans atCopied⟩

include D in
/-- The actual pre-scan cut removes only the final control row. It preserves
every recovered strict prefix of every earlier copy stage. -/
theorem copies_cut_stage_prefix (proper : IBLP.ProperMarks a)
    {last : IBLP.Row} {p m h : Nat} {b c : IBLP.Pattern}
    (hlast : a.getLast? = some last) (hp : last.p = some p)
    (run : IBLP.rawCopies m a = some b) (cut : IBLP.cut b = some c)
    (within : h ≤ m) :
    c.length = a.length + m * (a.length - p) - 1 ∧
      ∃ middle, IBLP.rawCopies h a = some middle ∧
        middle.length = a.length + h * (a.length - p) ∧
        ∀ i, i < a.length + h * (a.length - p) → IBLP.rowAt c i = IBLP.rowAt middle i := by
  have length := (D.rawCopies_length_control proper hlast hp run).1
  obtain ⟨middle, first, middleLength, unchanged⟩ := D.rawCopies_stage_prefix proper hlast hp run within
  have monotone : h * (a.length - p) ≤ m * (a.length - p) := Nat.mul_le_mul_right _ within
  refine ⟨by rw [IBLP.cut_length cut, length], middle, first, middleLength, ?_⟩
  intro i before
  rw [(IBLP.cut_decomposition cut).2, IBLP.rowAt_take (by omega : i ≤ b.length - 1)]
  exact unchanged i before

end IBLP.FiniteBoundedData
