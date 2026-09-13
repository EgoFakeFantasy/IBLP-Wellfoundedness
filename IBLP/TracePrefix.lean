import IBLP.Trace

namespace IBLP

/-- An accurate descending history reads only rows at or below its start. -/
theorem Trace.congr_prefix {a b : Pattern} {bound target start : Nat} {rows : List Nat}
    (same : ∀ i, i < bound → rowAt b i = rowAt a i)
    (before : start < bound) (h : Trace a target start rows) : Trace b target start rows := by
  induction h with
  | done => exact .done
  | @step start next tail ht hp hn inner ih =>
    have pred : predecessor b start = predecessor a start := by
      simp only [predecessor, same _ before]
    exact .step ht (pred.trans hp) hn (ih (by omega))

/-- A successful mark trace is unchanged whenever the carrier and all
potentially visited factor rows lie in a common strict prefix. -/
theorem markTrace_prefix {a b : Pattern} {bound r mark : Nat} {trace : List Nat}
    (same : ∀ i, i < bound → rowAt b i = rowAt a i)
    (carrierBefore : r < bound) (markBefore : mark < bound)
    (computed : markTrace a r mark = some trace) : markTrace b r mark = some trace := by
  unfold markTrace at computed ⊢
  obtain ⟨row, atRow, rest⟩ := Option.bind_eq_some_iff.mp computed
  rw [same r carrierBefore, atRow]
  dsimp only [Bind.bind, Option.bind] at rest ⊢
  split at rest
  · rename_i member
    rw [if_pos member]
    split at rest
    · rename_i legal
      rw [if_pos legal]
      obtain ⟨target, paired, value⟩ := Option.bind_eq_some_iff.mp rest
      rw [paired]
      exact traceFrom_iff.mpr ((traceFrom_iff.mp value).congr_prefix same markBefore)
    · simp at rest
  · simp at rest

end IBLP
