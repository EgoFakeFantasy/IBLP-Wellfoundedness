import IBLP.Realization.TraceGraphAbsolute

namespace IBLP.FiniteBoundedData
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a b : IBLP.Pattern}
  (D : FiniteBoundedData stage a) (E : FiniteBoundedData stage b)

def RowGraphsEqual (r s : Nat) : Prop :=
  ∀ (hr : 0 < r ∧ r ≤ a.length) (hs : 0 < s ∧ s ≤ b.length), D.graph ⟨r, hr⟩ = E.graph ⟨s, hs⟩

/-- Reindexing a p-chain with the same ordered list of actual row graphs
preserves its entire internal composite graph, not only its named edges. -/
theorem traceGraph_congr_rows {target start target' start' : Nat} {rows rows' : List Nat}
    (h : FactorTrace a target start rows) (h' : FactorTrace b target' start' rows')
    (matched : List.Forall₂ (D.RowGraphsEqual E) rows rows') : D.traceGraph h = E.traceGraph h' := by
  apply Subtype.ext
  apply D.traceGraph_congr_values E h h'
  exact matched.imp (by intro r s same hr hs; exact congrArg Subtype.val (same hr hs))

end IBLP.FiniteBoundedData