import IBLP.Realization.InternalTraceGraph
import IBLP.Model.CompositionImage

namespace IBLP
open FullMarkedBLP
universe u

theorem ModelStage.RepresentsBoundedMap.graph_unique {stage : ModelStage.{u}}
    {alpha beta : Ordinal.{u}} {f g : stage.model.Element} {k : stage.BoundedMap alpha beta}
    (hf : stage.RepresentsBoundedMap f k) (hg : stage.RepresentsBoundedMap g k) : f = g := by
  apply Subtype.ext
  apply functionGraph_ext hf.1 hg.1
  intro x y
  rw [hf.graph_exact, hg.graph_exact]

theorem ModelStage.RepresentsBoundedMap.congr_values {stage : ModelStage.{u}}
    {alpha beta gamma delta : Ordinal.{u}} {graph : stage.model.Element}
    {k : stage.BoundedMap alpha beta} (h : stage.RepresentsBoundedMap graph k)
    (l : stage.BoundedMap gamma delta) (domainEq : alpha = gamma)
    (values : ∀ x y, x.val = y.val → (k x).val = (l y).val) :
    stage.RepresentsBoundedMap graph l := by
  subst gamma
  refine ⟨isFunc_retarget h.1 ?_, ?_⟩
  · intro a b edge
    obtain ⟨x, _, hx⟩ := (h.graph_exact a b).mp edge
    rw [← hx, values x x rfl]
    exact (stage.mem_hierarchy _ _).mpr (l x).property
  · intro x
    rw [← values x x rfl]
    exact h.2 x

theorem ModelStage.compatibleComposition_spec (stage : ModelStage.{u})
    {alpha beta gamma delta : Ordinal.{u}} (ha : Order.IsSuccLimit alpha)
    (k : stage.BoundedMap alpha beta) (l : stage.BoundedMap gamma delta) (fits : delta ≤ alpha)
    {outer inner result : stage.model.Element} (hk : stage.RepresentsBoundedMap outer k)
    (hl : stage.RepresentsBoundedMap inner l)
    (hp : stage.RepresentsBoundedMap result (stage.compatibleCompose ha k l fits)) :
    graphCompositionSpec inner.val outer.val result.val := by
  intro a b
  rw [hp.graph_exact]
  constructor
  · rintro ⟨x, rfl, rfl⟩
    rw [stage.compatibleCompose_val]
    exact ⟨(l x).val, hl.2 x, hk.2 (stage.rankLift (Order.succ_le_succ fits) (l x))⟩
  · rintro ⟨y, first, second⟩
    obtain ⟨x, hx, hxy⟩ := (hl.graph_exact a y).mp first
    obtain ⟨v, hv, hvb⟩ := (hk.graph_exact y b).mp second
    have same : v = stage.rankLift (Order.succ_le_succ fits) (l x) := Subtype.ext (hv.trans hxy.symm)
    refine ⟨x, hx, ?_⟩
    rw [stage.compatibleCompose_val, ← same]
    exact hvb

namespace FactorTrace
variable {stage : ModelStage.{u}} {a : Pattern} {theta : Nat → Ordinal.{u}}
  (R : InternalTraceRows stage a theta) {paired : Nat}

theorem internalCompositeGraph_single {r : Nat} (hp : predecessor a r = some paired) (hn : paired < r)
    (graphs : ∀ s ∈ [r], ∃ g : stage.model.Element, stage.RepresentsBoundedMap g (R.map s))
    {graph : stage.model.Element} (rep : stage.RepresentsBoundedMap graph (R.map r)) :
    (FactorTrace.single hp hn).internalCompositeGraph R graphs = graph := by
  apply ((FactorTrace.single hp hn).internalCompositeGraph_represents R graphs).graph_unique
  apply rep.congr_val
  intro x
  have h := (FactorTrace.single hp hn).internalComposite_val R x
  exact (congrArg Subtype.val (stage.weakAction_on_domain (R.map r) x)).symm.trans h.symm

theorem internalCompositeGraph_cons_spec {r next : Nat} {tail : List Nat}
    (hp : predecessor a r = some next) (hn : next < r) (inner : FactorTrace a paired next tail)
    (graphs : ∀ s ∈ r :: tail, ∃ g : stage.model.Element, stage.RepresentsBoundedMap g (R.map s))
    (innerGraphs : ∀ s ∈ tail, ∃ g : stage.model.Element, stage.RepresentsBoundedMap g (R.map s))
    {outer : stage.model.Element} (outerRep : stage.RepresentsBoundedMap outer (R.map r)) :
    graphCompositionSpec (inner.internalCompositeGraph R innerGraphs).val outer.val
      ((FactorTrace.cons hp hn inner).internalCompositeGraph R graphs).val := by
  let fits := (inner.bound_interval R.actions).2.trans (R.adjacent_domain r next hp)
  apply stage.compatibleComposition_spec (R.source_limit r) (R.map r) (inner.internalComposite R) fits outerRep
    (inner.internalCompositeGraph_represents R innerGraphs)
  apply ((FactorTrace.cons hp hn inner).internalCompositeGraph_represents R graphs).congr_values
    (stage.compatibleCompose (R.source_limit r) (R.map r) (inner.internalComposite R) fits)
    (FactorTrace.inputBound_cons R.actions hp hn inner)
  intro x y same
  have h := stage.compatibleCompose_weakAction (R.source_limit r) (R.map r) (inner.internalComposite R) fits
    (stage.rankInclude _ y)
  rw [stage.weakAction_on_domain, inner.internalComposite_weakAction R] at h
  have parent := (FactorTrace.cons hp hn inner).internalComposite_val R x
  have step := congrArg (fun F : CutAction stage.cutSpace => (F.act (stage.rankInclude _ x)).val)
    (FactorTrace.word_cons R.actions hp hn inner)
  have parent' := parent.trans step
  have inputs : stage.rankInclude _ x = stage.rankInclude _ y := Subtype.ext same
  rw [inputs] at parent'
  exact parent'.trans (congrArg Subtype.val h).symm

end FactorTrace
end IBLP
