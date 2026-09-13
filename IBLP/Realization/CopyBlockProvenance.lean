import IBLP.Realization.CopyTailProvenance
import IBLP.TracePrefix

namespace IBLP.MarkedRealization
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (R : MarkedRealization stage a)

include R in
/-- The exact original mark and bottom transition in any completed copy
block, including blocks preserved by subsequent copies. -/
theorem rawCopies_block_mark_origin {last row : IBLP.Row} {p m k r mark bottom : Nat}
    {b : IBLP.Pattern} {trace : List Nat}
    (hlast : a.getLast? = some last) (hp : last.p = some p)
    (run : IBLP.rawCopies m a = some b) (within : k < m)
    (lower : a.length + k * (a.length - p) ≤ r)
    (upper : r < a.length + (k + 1) * (a.length - p))
    (atRow : IBLP.rowAt b r = some row) (marked : mark ∈ row.marks)
    (computed : IBLP.markTrace b r mark = some trace)
    (bottomAt : IBLP.fromRight trace 2 = some bottom) :
    ∃ original oldMark oldTrace oldBottom,
      IBLP.rowAt a (r - (k + 1) * (a.length - p)) = some original ∧
      oldMark ∈ original.marks ∧
      IBLP.markTrace a (r - (k + 1) * (a.length - p)) oldMark = some oldTrace ∧
      IBLP.fromRight oldTrace 2 = some oldBottom ∧
      bottom = (if p ≤ oldBottom then oldBottom + (k + 1) * (a.length - p) else oldBottom) ∧
      (p ≤ oldBottom → trace.dropLast = oldTrace.dropLast.map (· + (k + 1) * (a.length - p))) := by
  obtain ⟨middle, first, _, unchanged⟩ :=
    R.data.rawCopies_stage_prefix R.proper hlast hp run (Nat.succ_le_of_lt within)
  obtain ⟨nextStage, _, S, _, _⟩ := R.rawCopies_realization_exists (k + 1) first
  have atMiddle := (unchanged r upper).symm.trans atRow
  have below := IBLP.Row.properMark_lt (S.data.valid _ _ atMiddle)
    (S.proper row (rowAt_mem atMiddle) mark marked)
  have middleComputed := IBLP.markTrace_prefix (fun i hi => (unchanged i hi).symm)
    upper (below.trans upper) computed
  have pred : IBLP.predecessor a a.length = some p := by
    simp [IBLP.predecessor, IBLP.getLast_rowAt hlast, hp]
  have pn := IBLP.predecessor_lt R.data.valid R.data.shapes pred
  apply R.rawCopies_tail_mark_origin hlast hp first _ upper atMiddle marked middleComputed bottomAt
  rw [Nat.succ_mul]
  omega

include R in
/-- Manuscript 6.1 at copy exit: a bottom outside the original unscanned
prefix forces every nonterminal factor into the carrier's own copy block. -/
theorem rawCopies_block_active_factors {last row : IBLP.Row} {p m k r mark bottom : Nat}
    {b : IBLP.Pattern} {trace : List Nat}
    (hlast : a.getLast? = some last) (hp : last.p = some p)
    (run : IBLP.rawCopies m a = some b) (within : k < m)
    (lower : a.length + k * (a.length - p) ≤ r)
    (upper : r < a.length + (k + 1) * (a.length - p))
    (atRow : IBLP.rowAt b r = some row) (marked : mark ∈ row.marks)
    (computed : IBLP.markTrace b r mark = some trace)
    (bottomAt : IBLP.fromRight trace 2 = some bottom) (active : a.length ≤ bottom) :
    ∀ t ∈ trace.dropLast, a.length + k * (a.length - p) ≤ t ∧ t < r := by
  obtain ⟨original, oldMark, oldTrace, oldBottom, originalAt, oldMarked,
    oldComputed, oldBottomAt, bottomValue, factorsValue⟩ :=
    R.rawCopies_block_mark_origin hlast hp run within lower upper atRow marked computed bottomAt
  have pred : IBLP.predecessor a a.length = some p := by
    simp [IBLP.predecessor, IBLP.getLast_rowAt hlast, hp]
  have pn := IBLP.predecessor_lt R.data.valid R.data.shapes pred
  have full : p ≤ oldBottom := by
    by_contra outside
    rw [if_neg outside] at bottomValue
    omega
  obtain ⟨source, history, paired, historyAt, factors, _⟩ :=
    R.marks _ original oldMark originalAt oldMarked
  have sameHistory : history = oldTrace := Option.some.inj (historyAt.symm.trans oldComputed)
  subst history
  have shape := (IBLP.markTrace_spec originalAt paired oldComputed).2.2.unique factors.toTrace
  have tail := factors.tail_of_bottom (by rw [← shape]; exact oldBottomAt) full
  have below := IBLP.Row.properMark_lt (R.data.valid _ _ originalAt)
    (R.proper original (rowAt_mem originalAt) oldMark oldMarked)
  intro t member
  rw [factorsValue full] at member
  obtain ⟨old, oldMember, image⟩ := List.mem_map.mp member
  have oldLower := tail old oldMember
  have oldUpper := (factors.member_le_start old oldMember).trans_lt below
  rw [Nat.succ_mul] at image oldUpper
  constructor <;> omega

end IBLP.MarkedRealization
