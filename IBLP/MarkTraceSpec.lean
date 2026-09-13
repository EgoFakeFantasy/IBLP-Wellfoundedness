import IBLP.Trace

namespace IBLP

theorem markTrace_spec {a : Pattern} {r b target : Nat} {row : Row} {trace : List Nat}
    (hr : rowAt a r = some row) (paired : row.columns[row.columns.idxOf b - row.step]? = some target)
    (computed : markTrace a r b = some trace) :
    b ∈ row.columns ∧ row.step ≤ row.columns.idxOf b ∧ Trace a target b trace := by
  unfold markTrace at computed
  obtain ⟨selected, atSelected, computed⟩ := Option.bind_eq_some_iff.mp computed
  have same : selected = row := Option.some.inj (atSelected.symm.trans hr)
  subst selected
  split at computed
  · rename_i member
    dsimp only at computed
    split at computed
    · rename_i legal
      obtain ⟨t, atTarget, value⟩ := Option.bind_eq_some_iff.mp computed
      have sameTarget : t = target := Option.some.inj (atTarget.symm.trans paired)
      subst t
      exact ⟨member, legal, traceFrom_iff.mp value⟩
    · simp at computed
  · simp at computed

end IBLP
