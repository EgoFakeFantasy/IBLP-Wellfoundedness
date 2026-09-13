import IBLP.Realization.InternalTrace
import IBLP.Realization.BoundedMapGraph

namespace IBLP
open FullMarkedBLP
universe u

namespace ModelStage

/-- Ordinary composition graphs are sets in M. Their codomain is tightened to
the computed natural target, using the actual compatible composite values. -/
theorem compatibleCompose_graph_exists (stage : ModelStage.{u})
    {alpha beta gamma delta : Ordinal.{u}} (ha : Order.IsSuccLimit alpha)
    (k : stage.BoundedMap alpha beta) (l : stage.BoundedMap gamma delta) (fits : delta ≤ alpha)
    {outer inner : stage.model.Element}
    (hk : stage.RepresentsBoundedMap outer k) (hl : stage.RepresentsBoundedMap inner l) :
    ∃ graph : stage.model.Element,
      stage.RepresentsBoundedMap graph (stage.compatibleCompose ha k l fits) := by
  let included := stage.hierarchy_mono (Order.succ_le_succ fits)
  let graph := stage.compGraph inner outer (stage.hierarchy (Order.succ gamma))
    (stage.hierarchy (Order.succ delta)) (stage.hierarchy (Order.succ alpha))
    (stage.hierarchy (Order.succ beta)) hl.1 hk.1 included
  have function : ZFSet.IsFunc (stage.hierarchy (Order.succ gamma)).val
      (stage.hierarchy (Order.succ beta)).val graph.val :=
    stage.compGraph_function inner outer _ _ _ _ hl.1 hk.1 included
  have edges (x z : ZFSet.{u}) : ZFSet.pair x z ∈ graph.val ↔
      ∃ y : ZFSet.{u}, ZFSet.pair x y ∈ inner.val ∧ ZFSet.pair y z ∈ outer.val :=
    stage.compGraph_edge_iff inner outer _ _ _ _ hl.1 hk.1 included x z
  have value (a b : ZFSet.{u}) (edge : ZFSet.pair a b ∈ graph.val) :
      ∃ x : stage.model.RankElement (Order.succ gamma),
        x.val = a ∧ (stage.compatibleCompose ha k l fits x).val = b := by
    obtain ⟨y, hxy, hyz⟩ := (edges a b).mp edge
    obtain ⟨x, hx, hxy⟩ := (hl.graph_exact a y).mp hxy
    obtain ⟨v, hv, hvb⟩ := (hk.graph_exact y b).mp hyz
    have compatible : v = stage.rankLift (Order.succ_le_succ fits) (l x) :=
      Subtype.ext (hv.trans hxy.symm)
    refine ⟨x, hx, ?_⟩
    rw [stage.compatibleCompose_val, ← compatible]
    exact hvb
  refine ⟨graph, isFunc_retarget function ?_, ?_⟩
  · intro a b edge
    obtain ⟨x, _, hb⟩ := value a b edge
    rw [← hb]
    exact (stage.mem_hierarchy _ _).mpr (stage.compatibleCompose ha k l fits x).property
  · intro x
    apply (edges _ _).mpr
    refine ⟨(l x).val, hl.2 x, ?_⟩
    have edge := hk.2 (stage.rankLift (Order.succ_le_succ fits) (l x))
    rw [stage.compatibleCompose_val]
    exact edge

end ModelStage

namespace FactorTrace
variable {stage : ModelStage.{u}} {a : Pattern} {theta : Nat → Ordinal.{u}}
  (R : InternalTraceRows stage a theta) {target start : Nat} {rows : List Nat}

/-- Only graphs of the finitely many factors actually in this trace are used. -/
theorem internalGraphComposite_exists (h : FactorTrace a target start rows)
    (graphs : ∀ r ∈ rows, ∃ graph : stage.model.Element, stage.RepresentsBoundedMap graph (R.map r)) :
    ∃ k : stage.BoundedMap (h.inputBound R.actions) (h.word R.actions).bound,
      ∃ graph : stage.model.Element, stage.RepresentsBoundedMap graph k ∧
        ∀ z, stage.weakAction k z = (h.word R.actions).act z := by
  revert graphs
  induction h with
  | @single r hp hn =>
    intro graphs
    obtain ⟨graph, represented⟩ := graphs r (by simp)
    exact ⟨R.map r, graph, represented, fun _ => rfl⟩
  | @cons r next tail hp hn inner ih =>
    intro graphs
    obtain ⟨k, inside, represented, weak⟩ := ih (fun s hs => graphs s (List.mem_cons_of_mem _ hs))
    obtain ⟨outside, outerRep⟩ := graphs r (by simp)
    have fits : (inner.word R.actions).bound ≤ R.source r :=
      (inner.bound_interval R.actions).2.trans (R.adjacent_domain r next hp)
    obtain ⟨graph, compositeRep⟩ :=
      stage.compatibleCompose_graph_exists (R.source_limit r) (R.map r) k fits outerRep represented
    rw [word_cons R.actions hp hn inner, inputBound_cons R.actions hp hn inner, CutAction.comp_bound]
    refine ⟨stage.compatibleCompose (R.source_limit r) (R.map r) k fits, graph, compositeRep, ?_⟩
    intro z
    exact (stage.compatibleCompose_weakAction (R.source_limit r) (R.map r) k fits z).trans
      (congrArg (stage.weakAction (R.map r)) (weak z))

/-- The previously constructed genuine trace embedding has a graph in M. -/
theorem internalComposite_graph_exists (h : FactorTrace a target start rows)
    (graphs : ∀ r ∈ rows, ∃ graph : stage.model.Element, stage.RepresentsBoundedMap graph (R.map r)) :
    ∃ graph : stage.model.Element, stage.RepresentsBoundedMap graph (h.internalComposite R) := by
  obtain ⟨k, graph, represented, weak⟩ := h.internalGraphComposite_exists R graphs
  refine ⟨graph, represented.congr_val ?_⟩
  intro x
  have values := weak (stage.rankInclude _ x)
  rw [stage.weakAction_on_domain] at values
  exact (congrArg (fun z : stage.model.Element => z.val) values).trans (h.internalComposite_val R x).symm

noncomputable def internalCompositeGraph (h : FactorTrace a target start rows)
    (graphs : ∀ r ∈ rows, ∃ graph : stage.model.Element, stage.RepresentsBoundedMap graph (R.map r)) :
    stage.model.Element := (h.internalComposite_graph_exists R graphs).choose

theorem internalCompositeGraph_represents (h : FactorTrace a target start rows)
    (graphs : ∀ r ∈ rows, ∃ graph : stage.model.Element, stage.RepresentsBoundedMap graph (R.map r)) :
    stage.RepresentsBoundedMap (h.internalCompositeGraph R graphs) (h.internalComposite R) :=
  (h.internalComposite_graph_exists R graphs).choose_spec

theorem internalCompositeGraph_elementary (h : FactorTrace a target start rows)
    (graphs : ∀ r ∈ rows, ∃ graph : stage.model.Element, stage.RepresentsBoundedMap graph (R.map r)) :
    stage.InternalGraphElementary (h.inputBound R.actions) (h.word R.actions).bound
      (h.internalCompositeGraph R graphs) :=
  (h.internalCompositeGraph_represents R graphs).toInternalGraphElementary

theorem internalCompositeGraph_exact (h : FactorTrace a target start rows)
    (graphs : ∀ r ∈ rows, ∃ graph : stage.model.Element, stage.RepresentsBoundedMap graph (R.map r))
    (x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ (h.internalCompositeGraph R graphs).val ↔
      ∃ input : stage.model.RankElement (Order.succ (h.inputBound R.actions)),
        input.val = x ∧ (h.internalComposite R input).val = y :=
  (h.internalCompositeGraph_represents R graphs).graph_exact x y

end FactorTrace
end IBLP
