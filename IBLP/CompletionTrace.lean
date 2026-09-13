import IBLP.RowUpdate
import IBLP.MarkTraceSpec

namespace IBLP

theorem FactorTrace.of_predecessor_eq {a b : Pattern} (same : ∀ i, predecessor b i = predecessor a i)
    {target start : Nat} {rows : List Nat} (h : FactorTrace a target start rows) :
    FactorTrace b target start rows := by
  induction h with
  | single hp hn => exact .single (by rwa [same]) hn
  | cons hp hn inner ih => exact .cons (by rwa [same]) hn ih

theorem Trace.of_predecessor_eq {a b : Pattern} (same : ∀ i, predecessor b i = predecessor a i)
    {target start : Nat} {rows : List Nat} (h : Trace a target start rows) : Trace b target start rows := by
  induction h with
  | done => exact .done
  | step ht hp hn inner ih => exact .step ht (by rwa [same]) hn ih

theorem Row.CompletionGeometry.set_predecessor {a : Pattern} {r mark : Nat} {row : Row}
    {sources : List Nat} (hr : rowAt a r = some row) (valid : row.BasicValid r)
    (shape : row.OrdinaryShape) (C : row.CompletionGeometry r mark sources) :
    ∀ i, predecessor (a.set (r - 1) (completeMarkRow row mark sources)) i = predecessor a i := by
  obtain ⟨p, hp⟩ := fromRight_exists (xs := row.columns) (k := row.step + 1)
    (by omega) (by have := Row.step_lt_length shape; omega)
  exact predecessor_set_eq hr ((C.preserves_p valid shape hp).trans hp.symm)

theorem FactorTrace.completion {a : Pattern} {r mark : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (valid : row.BasicValid r) (shape : row.OrdinaryShape)
    (C : row.CompletionGeometry r mark sources) {target start : Nat} {rows : List Nat}
    (h : FactorTrace a target start rows) :
    FactorTrace (a.set (r - 1) (completeMarkRow row mark sources)) target start rows :=
  h.of_predecessor_eq (C.set_predecessor hr valid shape)

theorem Trace.completion {a : Pattern} {r mark : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (valid : row.BasicValid r) (shape : row.OrdinaryShape)
    (C : row.CompletionGeometry r mark sources) {target start : Nat} {rows : List Nat}
    (h : Trace a target start rows) :
    Trace (a.set (r - 1) (completeMarkRow row mark sources)) target start rows :=
  h.of_predecessor_eq (C.set_predecessor hr valid shape)

end IBLP
