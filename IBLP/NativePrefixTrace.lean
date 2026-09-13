import IBLP.NativeRows
import IBLP.PrefixGeometry

namespace IBLP

theorem FactorTrace.native_prefix {a b : Pattern} {r target start : Nat} {sources rows : List Nat}
    (run : native a r = some (b, sources)) (h : FactorTrace a target start rows) (before : start < r) :
    FactorTrace b target start rows := by
  induction h with
  | single hp hn => exact .single (by simpa only [predecessor, native_prefix_rowAt run before] using hp) hn
  | cons hp hn inner ih =>
    exact .cons (by simpa only [predecessor, native_prefix_rowAt run before] using hp) hn (ih (by omega))

theorem Trace.native_prefix {a b : Pattern} {r target start : Nat} {sources rows : List Nat}
    (run : native a r = some (b, sources)) (h : Trace a target start rows) (before : start < r) :
    Trace b target start rows := by
  induction h with
  | done => exact .done
  | step ht hp hn inner ih =>
    exact .step ht (by simpa only [predecessor, native_prefix_rowAt run before] using hp) hn (ih (by omega))

theorem native_prefix_markTrace {a b : Pattern} {r i mark source : Nat} {row : Row} {sources trace : List Nat}
    (run : native a r = some (b, sources)) (before : i < r) (hr : rowAt a i = some row)
    (below : mark < i) (paired : row.columns[row.columns.idxOf mark - row.step]? = some source)
    (computed : markTrace a i mark = some trace) : markTrace b i mark = some trace := by
  obtain ⟨member, index, history⟩ := markTrace_spec hr paired computed
  have history' := history.native_prefix run (by omega : mark < r)
  have newRow := (native_prefix_rowAt run before).trans hr
  simp [markTrace, newRow, member, index, paired, traceFrom_iff.mpr history']

end IBLP
