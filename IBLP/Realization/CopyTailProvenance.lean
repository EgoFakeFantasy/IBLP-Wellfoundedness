import IBLP.Realization.ActiveCopyTrace
import IBLP.Realization.CopyBlockOrigin
import IBLP.Realization.FiniteCopiesRealized

namespace IBLP.MarkedRealization
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (R : MarkedRealization stage a)

include R in
/-- Every stored mark in the final copied tail has an actual original mark.
Crossing bottoms stay below the original control predecessor. Full-copy
bottoms and the entire nonterminal factor list translate once per copy.
The final control row is excluded, as it is removed before scanning. -/
theorem rawCopies_tail_mark_origin {last row : IBLP.Row} {p m r mark bottom : Nat}
    {b : IBLP.Pattern} {trace : List Nat}
    (hlast : a.getLast? = some last) (hp : last.p = some p)
    (run : IBLP.rawCopies m a = some b)
    (lower : p + m * (a.length - p) ≤ r)
    (upper : r < a.length + m * (a.length - p))
    (atRow : IBLP.rowAt b r = some row) (marked : mark ∈ row.marks)
    (computed : IBLP.markTrace b r mark = some trace)
    (bottomAt : IBLP.fromRight trace 2 = some bottom) :
    ∃ original oldMark oldTrace oldBottom,
      IBLP.rowAt a (r - m * (a.length - p)) = some original ∧
      oldMark ∈ original.marks ∧
      IBLP.markTrace a (r - m * (a.length - p)) oldMark = some oldTrace ∧
      IBLP.fromRight oldTrace 2 = some oldBottom ∧
      bottom = (if p ≤ oldBottom then oldBottom + m * (a.length - p) else oldBottom) ∧
      (p ≤ oldBottom → trace.dropLast = oldTrace.dropLast.map (· + m * (a.length - p))) := by
  induction m generalizing b r row mark trace bottom with
  | zero =>
    have same : a = b := Option.some.inj run
    subst b
    refine ⟨row, mark, trace, bottom, ?_, marked, ?_, bottomAt, ?_, ?_⟩
    · simpa using atRow
    · simpa using computed
    · simp
    · intro _; simp
  | succ m ih =>
    obtain ⟨before, first, rest⟩ := IBLP.rawCopies_split run (Nat.le_succ m)
    have copy : IBLP.rawCopy before = some b := by
      simpa [show m + 1 - m = 1 by omega, IBLP.rawCopies] using rest
    obtain ⟨beforeLength, control, atControl, controlP⟩ :=
      R.data.rawCopies_length_control R.proper hlast hp first
    obtain ⟨middleStage, _, S, _, _⟩ := R.rawCopies_realization_exists m first
    have pred : IBLP.predecessor a a.length = some p := by
      simp [IBLP.predecessor, IBLP.getLast_rowAt hlast, hp]
    have pn := IBLP.predecessor_lt R.data.valid R.data.shapes pred
    have width : before.length - (p + m * (a.length - p)) = a.length - p := by omega
    rw [Nat.succ_mul] at lower upper
    obtain ⟨source, sourceLower, _, owner, rowCopy⟩ :=
      IBLP.rawCopy_row_origin copy atControl controlP (by omega) atRow
    rw [width] at owner
    obtain ⟨sourceRow, atSource, _⟩ := Option.bind_eq_some_iff.mp rowCopy
    have sourceUpper : source < a.length + m * (a.length - p) := by omega
    have nonempty := IBLP.rowAt_pos (IBLP.getLast_rowAt atControl)
    have headBound : 0 < control.columns.length := by
      have := (S.data.valid _ _ (IBLP.getLast_rowAt atControl)).2.1
      omega
    let minimum := control.columns[0]'headBound
    have hm : control.columns.head? = some minimum := by
      simp only [List.head?_eq_getElem?, List.getElem?_eq_getElem headBound, minimum]
    obtain ⟨priorMark, priorTrace, priorBottom, copiedTrace, priorMarked, markImage,
      priorComputed, priorBottomAt, copiedComputed, copiedBottomAt⟩ :=
      S.copied_mark_bottom_origin nonempty copy atControl hm controlP atSource sourceLower rowCopy marked
    rw [width, ← owner] at copiedComputed
    have sameTrace : copiedTrace = trace := Option.some.inj (copiedComputed.symm.trans computed)
    subst copiedTrace
    rw [width] at copiedBottomAt
    have bottomValue := Option.some.inj (bottomAt.symm.trans copiedBottomAt)
    obtain ⟨original, oldMark, oldTrace, oldBottom, originalAt, oldMarked,
      oldComputed, oldBottomAt, priorValue, priorFactors⟩ :=
      ih first sourceLower sourceUpper atSource priorMarked priorComputed priorBottomAt
    have originalIndex : r - (m + 1) * (a.length - p) = source - m * (a.length - p) := by
      rw [Nat.succ_mul]
      omega
    refine ⟨original, oldMark, oldTrace, oldBottom, ?_, oldMarked, ?_, oldBottomAt, ?_, ?_⟩
    · simpa only [originalIndex] using originalAt
    · simpa only [originalIndex] using oldComputed
    · by_cases full : p ≤ oldBottom
      · rw [if_pos full] at priorValue ⊢
        have fullNow : p + m * (a.length - p) ≤ priorBottom := by omega
        rw [if_pos fullNow] at bottomValue
        rw [Nat.succ_mul]
        omega
      · rw [if_neg full] at priorValue ⊢
        have crossingNow : ¬p + m * (a.length - p) ≤ priorBottom := by omega
        rw [if_neg crossingNow] at bottomValue
        omega
    · intro full
      have fullNow : p + m * (a.length - p) ≤ priorBottom := by
        rw [if_pos full] at priorValue
        omega
      obtain ⟨target, imageTarget, _, _, _, expected⟩ :=
        S.fullCopy_trace_from_bottom nonempty copy atControl hm controlP atSource rowCopy
          priorMarked priorComputed priorBottomAt fullNow markImage
      rw [width, ← owner] at expected
      have value := Option.some.inj (computed.symm.trans expected)
      rw [value, List.dropLast_concat, priorFactors full, List.map_map]
      apply List.map_congr_left
      intro t _
      simp only [Function.comp_apply, Nat.succ_mul]
      omega

end IBLP.MarkedRealization
