import IBLP.Realization.InternalTraceGraph
import IBLP.Model.InaccessibleImage

namespace IBLP
open FullMarkedBLP
universe u

namespace FactorTrace
variable {stage : ModelStage.{u}} {a : Pattern} {theta : Nat → Ordinal.{u}}
  (R : InternalTraceRows stage a theta) {target start : Nat} {rows : List Nat}

theorem naturalBound_isSuccLimit (h : FactorTrace a target start rows) :
    Order.IsSuccLimit (h.word R.actions).bound :=
  stage.boundedMap_target_isSuccLimit (h.internalComposite R) (h.internal_inputBound_limit R)

/-- Inaccessibility of Delta follows from the actual elementary composite,
including its endpoint, rather than being postulated for the word. -/
theorem naturalBound_inaccessible (h : FactorTrace a target start rows)
    (sources : ∀ r ∈ rows, stage.model.InternalInaccessible (stage.ordinal (R.source r))) :
    stage.model.InternalInaccessible (stage.ordinal (h.word R.actions).bound) := by
  apply stage.boundedMap_endpoint_internalInaccessible (h.internalComposite R)
  exact sources (rows.getLast h.nonempty) (List.getLast_mem h.nonempty)

/-- All three bounds from (3.13), with the finite carrier-row bound included. -/
theorem carrier_bound (h : FactorTrace a target start rows) {carrier : Nat}
    (increasing : StrictMonoOn theta (Set.Iic (a.length + 1)))
    (inside : carrier ≤ a.length) (earlier : start < carrier) :
    theta start < (h.word R.actions).bound ∧
      (h.word R.actions).bound ≤ theta (start + 1) ∧ theta (start + 1) < theta (carrier + 1) := by
  have bounds := h.bound_interval R.actions
  refine ⟨bounds.1, bounds.2, ?_⟩
  exact increasing (by show start + 1 ≤ a.length + 1; omega)
    (by show carrier + 1 ≤ a.length + 1; omega) (by omega)

/-- A complete trace realization at its computed source and natural target,
with a real graph in M, endpoint action, paired-source action and inaccessible target. -/
theorem internal_realization (h : FactorTrace a target start rows)
    (graphs : ∀ r ∈ rows, ∃ graph : stage.model.Element, stage.RepresentsBoundedMap graph (R.map r))
    (sources : ∀ r ∈ rows, stage.model.InternalInaccessible (stage.ordinal (R.source r))) :
    ∃ graph : stage.model.Element,
      stage.InternalGraphElementary (h.inputBound R.actions) (h.word R.actions).bound graph ∧
      stage.model.InternalInaccessible (stage.ordinal (h.word R.actions).bound) ∧
      ZFSet.pair (theta target).toZFSet (theta start).toZFSet ∈ graph.val ∧
      ZFSet.pair (h.inputBound R.actions).toZFSet (h.word R.actions).bound.toZFSet ∈ graph.val := by
  refine ⟨h.internalCompositeGraph R graphs, h.internalCompositeGraph_elementary R graphs,
    h.naturalBound_inaccessible R sources, ?_, ?_⟩
  · have edge := (h.internalCompositeGraph_represents R graphs).2
      (stage.rankOrdinal ⟨theta target, Order.lt_succ_of_le (h.target_lt_inputBound R.actions).le⟩)
    rwa [h.internalComposite_predecessor R] at edge
  · have edge := (h.internalCompositeGraph_represents R graphs).2
      (stage.rankOrdinal (endpoint (h.inputBound R.actions)))
    rwa [h.internalComposite_endpoint R] at edge

/-- Manuscript (3.14) is an additional realization requirement on this row;
existence of the trace and its elementary word alone does not prove it. -/
def MarkCertificate (h : FactorTrace a target start rows) (carrier : Nat) : Prop :=
  CutAction.WeakAgreement (R.actions.action carrier) (h.word R.actions) (h.word R.actions).bound

theorem markCertificate_iff_allInputs (h : FactorTrace a target start rows) (carrier : Nat) :
    h.MarkCertificate R carrier ↔
      CutAction.AllInputAgreement (R.actions.action carrier) (h.word R.actions) (h.word R.actions).bound :=
  CutAction.weakAgreement_iff_allInputs (h.naturalBound_isSuccLimit R)

/-- A supplied mark certificate recovers the actual recorded ordinal edge. -/
theorem markCertificate_reads_predecessor (h : FactorTrace a target start rows) {carrier : Nat}
    (certificate : h.MarkCertificate R carrier) :
    stage.weakAction (R.map carrier) (stage.ordinal (theta target)) = stage.ordinal (theta start) := by
  have reverse : CutAction.WeakAgreement (h.word R.actions) (R.actions.action carrier)
      (h.word R.actions).bound := fun x z hx hz => (certificate x z hx hz).symm
  exact reverse.reads_edge stage.ordinalView (h.naturalBound_isSuccLimit R)
    (stage.ordinal (theta target)) (h.actual_predecessor_image R.actions)
    ⟨stage.rho (R.map carrier) (theta target), stage.weakAction_ordinal (R.map carrier) (theta target)⟩
    (h.bound_interval R.actions).1

theorem markCertificate_rho_edge (h : FactorTrace a target start rows) {carrier : Nat}
    (certificate : h.MarkCertificate R carrier) :
    stage.rho (R.map carrier) (theta target) = theta start := by
  have values := h.markCertificate_reads_predecessor R certificate
  rw [stage.weakAction_ordinal] at values
  simpa only [ModelStage.ordinal, Ordinal.rank_toZFSet] using
    congrArg (fun z : stage.model.Element => z.val.rank) values

end FactorTrace
end IBLP
