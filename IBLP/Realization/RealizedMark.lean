import IBLP.Realization.BoundedRealization

namespace IBLP
open FullMarkedBLP
universe u

namespace BoundedRealization
variable {stage : ModelStage.{u}} {a : Pattern} (R : BoundedRealization stage a)

/-- For every saved mark, (3.12)--(3.14) hold together for its computed trace:
the actual internal elementary graph, natural inaccessible endpoint, both
ordinal edges, all three carrier bounds, and the original weak certificate. -/
theorem mark_internal_realization {r b : Nat} {row : Row} (hr : rowAt a r = some row)
    (hb : b ∈ row.marks) :
    ∃ target trace,
      row.columns[row.columns.idxOf b - row.step]? = some target ∧
      markTrace a r b = some trace ∧
      ∃ h : FactorTrace a target b trace.dropLast, ∃ graph : stage.model.Element,
        stage.InternalGraphElementary
          (h.inputBound R.data.toFiniteTraceRows.toInternalTraceRows.actions)
          (h.word R.data.toFiniteTraceRows.toInternalTraceRows.actions).bound graph ∧
        stage.model.InternalInaccessible
          (stage.ordinal (h.word R.data.toFiniteTraceRows.toInternalTraceRows.actions).bound) ∧
        ZFSet.pair (R.data.point target).toZFSet (R.data.point b).toZFSet ∈ graph.val ∧
        ZFSet.pair (h.inputBound R.data.toFiniteTraceRows.toInternalTraceRows.actions).toZFSet
          (h.word R.data.toFiniteTraceRows.toInternalTraceRows.actions).bound.toZFSet ∈ graph.val ∧
        R.data.point b < (h.word R.data.toFiniteTraceRows.toInternalTraceRows.actions).bound ∧
        (h.word R.data.toFiniteTraceRows.toInternalTraceRows.actions).bound ≤ R.data.point (b + 1) ∧
        R.data.point (b + 1) < R.data.point (r + 1) ∧
        h.MarkCertificate R.data.toFiniteTraceRows.toInternalTraceRows r := by
  obtain ⟨target, trace, paired, computed, h, certificate⟩ := R.marks r row b hr hb
  obtain ⟨graph, elementary, inaccessible, pairedEdge, endpointEdge⟩ :=
    R.data.trace_internal_realization h
  have earlier := Row.properMark_lt (R.data.valid _ _ hr)
    (R.proper row (rowAt_mem hr) b hb)
  obtain ⟨lower, upper, carrier⟩ := h.carrier_bound R.data.toFiniteTraceRows.toInternalTraceRows
    R.data.point_increasing (rowAt_le_length hr) earlier
  exact ⟨target, trace, paired, computed, h, graph, elementary, inaccessible,
    pairedEdge, endpointEdge, lower, upper, carrier, certificate⟩

/-- The mark's semantic certificate reads the actual paired-source ordinal
edge from the saved carrier-row graph, through its canonical weak action. -/
theorem mark_ordinal_edge {r b : Nat} {row : Row} (hr : rowAt a r = some row)
    (hb : b ∈ row.marks) :
    ∃ target trace, row.columns[row.columns.idxOf b - row.step]? = some target ∧
      markTrace a r b = some trace ∧
      stage.weakAction (R.data.map ⟨r, rowAt_pos hr, rowAt_le_length hr⟩)
        (stage.ordinal (R.data.point target)) = stage.ordinal (R.data.point b) := by
  obtain ⟨target, trace, paired, computed, h, certificate⟩ := R.marks r row b hr hb
  have edge := h.markCertificate_reads_predecessor R.data.toFiniteTraceRows.toInternalTraceRows certificate
  refine ⟨target, trace, paired, computed, ?_⟩
  let input := stage.rankCut (R.data.toFiniteTraceRows.toInternalTraceRows.source r)
    (stage.ordinal (R.data.point target))
  have sourceSame := R.data.toFiniteTraceRows.source_valid ⟨r, rowAt_pos hr, rowAt_le_length hr⟩
  have cuts : input.val = (stage.rankCut (R.data.source r) (stage.ordinal (R.data.point target))).val := by
    change _ ∩ ZFSet.vonNeumann (R.data.toFiniteTraceRows.toInternalTraceRows.source r) = _
    rw [sourceSame]
    rfl
  have values := R.data.toFiniteTraceRows.map_valid_value
    ⟨r, rowAt_pos hr, rowAt_le_length hr⟩
    (stage.rankCut (R.data.source r) (stage.ordinal (R.data.point target))) input cuts
  apply Subtype.ext
  exact values.symm.trans (congrArg (fun z : stage.model.Element => z.val) edge)

end BoundedRealization
end IBLP
