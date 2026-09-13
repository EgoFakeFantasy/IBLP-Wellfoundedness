import IBLP.Realization.CopyBlockProvenance

namespace IBLP.MarkedRealization
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (R : MarkedRealization stage a)

include R in
/-- Recover an actual pre-cut carrier and trace for a mark in a copied
block. This applies also to the last row retained by the original cut. -/
theorem copies_cut_block_trace {last row : IBLP.Row} {p m k r mark : Nat}
    {b c : IBLP.Pattern} {trace : List Nat}
    (hlast : a.getLast? = some last) (hp : last.p = some p)
    (run : IBLP.rawCopies m a = some b) (cut : IBLP.cut b = some c) (within : k < m)
    (upper : r < a.length + (k + 1) * (a.length - p))
    (atRow : IBLP.rowAt c r = some row) (marked : mark ∈ row.marks)
    (computed : IBLP.markTrace c r mark = some trace) :
    IBLP.rowAt b r = some row ∧ IBLP.markTrace b r mark = some trace := by
  have length := (R.data.rawCopies_length_control R.proper hlast hp run).1
  have mulBound : (k + 1) * (a.length - p) ≤ m * (a.length - p) :=
    Nat.mul_le_mul_right (a.length - p) (Nat.succ_le_of_lt within)
  have before : r < b.length := by omega
  have unchanged : ∀ i, i < b.length → IBLP.rowAt c i = IBLP.rowAt b i := by
    intro i hi
    rw [(IBLP.cut_decomposition cut).2, IBLP.rowAt_take (by omega : i ≤ b.length - 1)]
  have originalAt := (unchanged r before).symm.trans atRow
  obtain ⟨nextStage, _, S, _, _⟩ := R.rawCopies_realization_exists m run
  have below := IBLP.Row.properMark_lt (S.data.valid _ _ originalAt)
    (S.proper row (rowAt_mem originalAt) mark marked)
  exact ⟨originalAt, IBLP.markTrace_prefix (fun i hi => (unchanged i hi).symm)
    before (below.trans before) computed⟩

include R in
/-- The full-copy provenance is available at the literal scan entrance,
after all raw copies and the original final cut. -/
theorem copies_cut_block_mark_origin {last row : IBLP.Row} {p m k r mark bottom : Nat}
    {b c : IBLP.Pattern} {trace : List Nat}
    (hlast : a.getLast? = some last) (hp : last.p = some p)
    (run : IBLP.rawCopies m a = some b) (cut : IBLP.cut b = some c) (within : k < m)
    (lower : a.length + k * (a.length - p) ≤ r)
    (upper : r < a.length + (k + 1) * (a.length - p))
    (atRow : IBLP.rowAt c r = some row) (marked : mark ∈ row.marks)
    (computed : IBLP.markTrace c r mark = some trace)
    (bottomAt : IBLP.fromRight trace 2 = some bottom) :
    ∃ original oldMark oldTrace oldBottom,
      IBLP.rowAt a (r - (k + 1) * (a.length - p)) = some original ∧
      oldMark ∈ original.marks ∧
      IBLP.markTrace a (r - (k + 1) * (a.length - p)) oldMark = some oldTrace ∧
      IBLP.fromRight oldTrace 2 = some oldBottom ∧
      bottom = (if p ≤ oldBottom then oldBottom + (k + 1) * (a.length - p) else oldBottom) ∧
      (p ≤ oldBottom → trace.dropLast = oldTrace.dropLast.map (· + (k + 1) * (a.length - p))) := by
  obtain ⟨originalAt, originalTrace⟩ :=
    R.copies_cut_block_trace hlast hp run cut within upper atRow marked computed
  exact R.rawCopies_block_mark_origin hlast hp run within lower upper originalAt marked originalTrace bottomAt

include R in
/-- At scan entrance every active stored mark has all nonterminal factors
in the same half-open copy block, strictly below its carrier. -/
theorem copies_cut_block_active_factors {last row : IBLP.Row} {p m k r mark bottom : Nat}
    {b c : IBLP.Pattern} {trace : List Nat}
    (hlast : a.getLast? = some last) (hp : last.p = some p)
    (run : IBLP.rawCopies m a = some b) (cut : IBLP.cut b = some c) (within : k < m)
    (lower : a.length + k * (a.length - p) ≤ r)
    (upper : r < a.length + (k + 1) * (a.length - p))
    (atRow : IBLP.rowAt c r = some row) (marked : mark ∈ row.marks)
    (computed : IBLP.markTrace c r mark = some trace)
    (bottomAt : IBLP.fromRight trace 2 = some bottom) (active : a.length ≤ bottom) :
    ∀ t ∈ trace.dropLast, a.length + k * (a.length - p) ≤ t ∧ t < r := by
  obtain ⟨originalAt, originalTrace⟩ :=
    R.copies_cut_block_trace hlast hp run cut within upper atRow marked computed
  exact R.rawCopies_block_active_factors hlast hp run within lower upper originalAt marked originalTrace bottomAt active

end IBLP.MarkedRealization
