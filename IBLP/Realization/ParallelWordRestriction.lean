import IBLP.Realization.MarkRestriction
import IBLP.Realization.CompletionMarks

namespace IBLP
open FullMarkedBLP
universe u

/-- Simultaneous restriction for any accurate parallel chain. Its actual
source and target may differ; the finite factor list identifies the saved
historical maps being restricted. -/
theorem FactorTrace.word_restriction_map {stage : ModelStage.{u}} {a b : Pattern}
    (D : FiniteBoundedData stage a) (E : FiniteBoundedData stage b)
    {target start target' start' : Nat} {rows : List Nat} {names : Nat → Nat}
    (h : FactorTrace a target start rows)
    (h' : FactorTrace b target' start' (rows.map names))
    (factors : ∀ i ∈ rows,
      CutRestriction (E.toFiniteTraceRows.toInternalTraceRows.actions.action (names i))
        (D.toFiniteTraceRows.toInternalTraceRows.actions.action i)) :
    CutRestriction (h'.word E.toFiniteTraceRows.toInternalTraceRows.actions)
      (h.word D.toFiniteTraceRows.toInternalTraceRows.actions) := by
  have general : ∀ rows (nonempty : rows ≠ []),
      (∀ i ∈ rows,
        CutRestriction (E.toFiniteTraceRows.toInternalTraceRows.actions.action (names i))
          (D.toFiniteTraceRows.toInternalTraceRows.actions.action i)) →
      CutRestriction
        (CutAction.listWord E.toFiniteTraceRows.toInternalTraceRows.actions.action (rows.map names)
          (by cases rows with
              | nil => exact False.elim (nonempty rfl)
              | cons => simp))
        (CutAction.listWord D.toFiniteTraceRows.toInternalTraceRows.actions.action rows nonempty) := by
    intro rows
    induction rows with
    | nil => intro nonempty; exact False.elim (nonempty rfl)
    | cons first tail ih =>
      intro nonempty restrictions
      cases tail with
      | nil => exact restrictions first (List.mem_cons_self ..)
      | cons next rest =>
        simp only [List.map_cons]
        rw [CutAction.listWord_cons E.toFiniteTraceRows.toInternalTraceRows.actions.action
          (names first) (names next :: rest.map names) (by simp),
          CutAction.listWord_cons D.toFiniteTraceRows.toInternalTraceRows.actions.action
            first (next :: rest) (by simp)]
        exact (restrictions first (List.mem_cons_self ..)).comp
          (ih (by simp) (fun i member => restrictions i (List.mem_cons_of_mem _ member)))
  exact general rows h.nonempty factors

namespace FiniteBoundedData

/-- Full weak certificates for a packet follow from the old certificate
and the actual restrictions of the parallel factors and carrier. This
uses the whole weak action, not only its values on distinguished points. -/
theorem completionHistoryPacket_of_parallel_restrictions
    {stage : ModelStage.{u}} {a b : Pattern}
    (D : FiniteBoundedData stage a) (E : FiniteBoundedData stage b)
    (oldOwner : FiniteRowIndex a) (owner : FiniteRowIndex b)
    {target mark base : Nat} {rows sources : List Nat} {names : Nat → Nat}
    (h : FactorTrace a target mark rows)
    (certificate : h.MarkCertificate D.toFiniteTraceRows.toInternalTraceRows oldOwner.val)
    (decreasing : sources.Pairwise (· > ·)) (before : base + sources.length < owner.val)
    (parallel : ∀ j s, sources.reverse[j]? = some s →
      FactorTrace b s (base + j + 1) (rows.map (fun i => names i + j + 1)))
    (carrier : CutRestriction (E.toFiniteTraceRows.toInternalTraceRows.actions.action owner.val)
      (D.toFiniteTraceRows.toInternalTraceRows.actions.action oldOwner.val))
    (factors : ∀ j, j < sources.length → ∀ i ∈ rows,
      CutRestriction (E.toFiniteTraceRows.toInternalTraceRows.actions.action (names i + j + 1))
        (D.toFiniteTraceRows.toInternalTraceRows.actions.action i)) :
    E.CompletionHistoryPacket owner.val base sources := by
  intro s member
  let j := (sources.filter (· < s)).length
  have atSource : sources.reverse[j]? = some s := by
    simpa only [List.filter_reverse, List.length_reverse] using
      FullMarkedBLP.sorted_get_at_rank decreasing.reverse (List.mem_reverse.mpr member)
  have bound : j < sources.length := List.length_filter_lt_length_iff_exists.mpr ⟨s, member, by simp⟩
  have h' := parallel j s atSource
  have restriction := h.word_restriction_map D E h' (factors j bound)
  have newCertificate := D.markCertificate_of_restrictions E oldOwner owner h h'
    (by omega) carrier restriction certificate
  have position : base + j + 1 = base + 1 + (sources.filter (· < s)).length := by dsimp [j]; omega
  refine ⟨rows.map (fun i => names i + j + 1), ?_⟩
  rw [← position]
  exact ⟨h', newCertificate⟩

end FiniteBoundedData
end IBLP
