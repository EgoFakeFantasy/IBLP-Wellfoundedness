import IBLP.Realization.InternalTraceRows
import IBLP.Model.InternalWeakTruncation
import IBLP.Model.BoundedComposition

namespace IBLP
open FullMarkedBLP
universe u

namespace InternalTraceRows
variable {stage : ModelStage.{u}} {a : Pattern} {theta : Nat → Ordinal.{u}}

/-- The abstract trace algebra is instantiated by actual elementary maps in
the current internal model. Every algebraic and ordinal field is proved. -/
noncomputable def actions (R : InternalTraceRows stage a theta) :
    TraceActions a stage.cutSpace stage.ordinalView theta where
  action := fun r => stage.boundedCutAction (R.source_limit r) (R.map r)
  source := R.source
  bound_eq := fun _ _ _ => rfl
  source_image := fun r _ _ => stage.rho_of_source_le (R.map r) le_rfl
  predecessor_edge := by
    intro r p hp
    change stage.rho (R.map r) (theta p) = theta r
    have ordinalEq : clippedOrdinal (R.source r) (theta p) =
        ⟨theta p, Order.lt_succ_of_le (R.source_gap r p hp).le⟩ :=
      Subtype.ext (min_eq_right (R.source_gap r p hp).le)
    unfold ModelStage.rho
    rw [ordinalEq]
    exact R.predecessor_ordinalAction hp
  source_gap := R.source_gap
  adjacent_domain := R.adjacent_domain
  strict_on_source := fun r _ _ => stage.rho_strictMonoOn (R.map r)
  ordinal_action := fun r _ _ => stage.weakAction_ordinal (R.map r)

end InternalTraceRows

namespace FactorTrace
variable {stage : ModelStage.{u}} {a : Pattern} {theta : Nat → Ordinal.{u}}
  (R : InternalTraceRows stage a theta) {target start : Nat} {rows : List Nat}

theorem internal_inputBound_limit (h : FactorTrace a target start rows) :
    Order.IsSuccLimit (h.inputBound R.actions) := R.source_limit (rows.getLast h.nonempty)

/-- The true elementary composite is constructed by successive restrictions
of the outer saved maps. Its target is the computed weak-word natural bound. -/
theorem internalComposite_exists (h : FactorTrace a target start rows) :
    ∃ k : stage.BoundedMap (h.inputBound R.actions) (h.word R.actions).bound,
      ∀ z, stage.weakAction k z = (h.word R.actions).act z := by
  induction h with
  | single hp hn => exact ⟨R.map _, fun _ => rfl⟩
  | @cons r next tail hp hn inner ih =>
    obtain ⟨k, hk⟩ := ih
    have fits : (inner.word R.actions).bound ≤ R.source r :=
      (inner.bound_interval R.actions).2.trans (R.adjacent_domain r next hp)
    rw [word_cons R.actions hp hn inner, inputBound_cons R.actions hp hn inner,
      CutAction.comp_bound]
    refine ⟨stage.compatibleCompose (R.source_limit r) (R.map r) k fits, ?_⟩
    intro z
    exact (stage.compatibleCompose_weakAction (R.source_limit r) (R.map r) k fits z).trans
      (congrArg (stage.weakAction (R.map r)) (hk z))

noncomputable def internalComposite (h : FactorTrace a target start rows) :
    stage.BoundedMap (h.inputBound R.actions) (h.word R.actions).bound :=
  (h.internalComposite_exists R).choose

theorem internalComposite_weakAction (h : FactorTrace a target start rows) (z : stage.model.Element) :
    stage.weakAction (h.internalComposite R) z = (h.word R.actions).act z :=
  (h.internalComposite_exists R).choose_spec z

theorem internalComposite_val (h : FactorTrace a target start rows)
    (x : stage.model.RankElement (Order.succ (h.inputBound R.actions))) :
    (h.internalComposite R x).val =
      ((h.word R.actions).act (stage.rankInclude _ x)).val := by
  have value := h.internalComposite_weakAction R (stage.rankInclude _ x)
  rw [stage.weakAction_on_domain] at value
  exact congrArg (fun z : stage.model.Element => z.val) value

theorem internalComposite_endpoint (h : FactorTrace a target start rows) :
    (h.internalComposite R (stage.rankOrdinal (endpoint (h.inputBound R.actions)))).val =
      (h.word R.actions).bound.toZFSet := by
  rw [h.internalComposite_val R]
  have value := h.actual_inputBound R.actions
  exact congrArg (fun z : stage.model.Element => z.val) value

theorem internalComposite_predecessor (h : FactorTrace a target start rows) :
    (h.internalComposite R (stage.rankOrdinal ⟨theta target,
      Order.lt_succ_of_le (h.target_lt_inputBound R.actions).le⟩)).val = (theta start).toZFSet := by
  rw [h.internalComposite_val R]
  have value := h.actual_predecessor_image R.actions
  exact congrArg (fun z : stage.model.Element => z.val) value

end FactorTrace
end IBLP
