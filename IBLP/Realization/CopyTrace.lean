import IBLP.Realization.CopyPredecessor

namespace IBLP
open FullMarkedBLP
universe u

theorem FactorTrace.start_mem {a : IBLP.Pattern} {target start : Nat} {rows : List Nat}
    (h : FactorTrace a target start rows) : start ∈ rows := by cases h <;> simp

namespace FiniteBoundedData
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (D : FiniteBoundedData stage a)

include D in
/-- Every nonterminal factor in the copied tail follows the translated p
chain. The terminal paired source may lie below p and uses its actual image. -/
theorem rawCopy_factorTrace (nonempty : 0 < a.length) {b : IBLP.Pattern} {last : IBLP.Row}
    {minimum p target start : Nat} {rows : List Nat} (copy : IBLP.rawCopy a = some b)
    (hlast : a.getLast? = some last) (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (trace : FactorTrace a target start rows) (tail : ∀ r ∈ rows, p ≤ r) :
    ∃ image, IBLP.copyEntry a.length last target = some image ∧
      FactorTrace b image (start + (a.length - p)) (rows.map (· + (a.length - p))) := by
  induction trace with
  | @single r pred smaller =>
    have inTail : p ≤ r := tail r (by simp)
    obtain ⟨image, value, next⟩ := D.rawCopy_predecessor_image nonempty copy hlast hm hp inTail pred
    have startImage := IBLP.copyEntry_tail (D.valid _ _ (IBLP.getLast_rowAt hlast)) hm hp inTail
    have bound : r ≤ a.length + 1 := (predecessor_row_index pred).2.trans (Nat.le_succ _)
    have less := D.copyEntry_strict nonempty (IBLP.getLast_rowAt hlast) hm hp bound smaller value startImage
    exact ⟨image, value, by simpa only [List.map_cons, List.map_nil] using FactorTrace.single next less⟩
  | @cons r next rows pred smaller inner ih =>
    obtain ⟨image, value, history⟩ := ih (fun s hs => tail s (List.mem_cons_of_mem r hs))
    have nextTail : p ≤ next := tail next (List.mem_cons_of_mem r inner.start_mem)
    have edge := D.rawCopy_predecessor_tail nonempty copy hlast hm hp nextTail pred
    exact ⟨image, value, by
      simpa only [List.map_cons] using
        FactorTrace.cons edge (Nat.add_lt_add_right smaller (a.length - p)) history⟩

include D in
theorem rawCopy_trace_compute (nonempty : 0 < a.length) {b : IBLP.Pattern} {last : IBLP.Row}
    {minimum p target start : Nat} {rows : List Nat} (copy : IBLP.rawCopy a = some b)
    (hlast : a.getLast? = some last) (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (trace : FactorTrace a target start rows) (tail : ∀ r ∈ rows, p ≤ r) :
    ∃ image, IBLP.copyEntry a.length last target = some image ∧
      IBLP.traceFrom b image (start + (a.length - p)) =
        some (rows.map (· + (a.length - p)) ++ [image]) := by
  obtain ⟨image, value, history⟩ := D.rawCopy_factorTrace nonempty copy hlast hm hp trace tail
  exact ⟨image, value, IBLP.traceFrom_iff.mpr history.toTrace⟩

end FiniteBoundedData
end IBLP
