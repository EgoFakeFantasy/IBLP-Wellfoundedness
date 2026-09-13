import IBLP.Model.BoundedMap
import IBLP.Model.GraphOperations

namespace IBLP
open FullMarkedBLP FirstOrder Language
universe u

/-- Keep the graph and domain, and tighten only its codomain after proving
the bound on every actual graph edge. -/
theorem isFunc_retarget {domain range smaller graph : ZFSet.{u}}
    (function : ZFSet.IsFunc domain range graph)
    (bounded : ∀ x y, ZFSet.pair x y ∈ graph → y ∈ smaller) :
    ZFSet.IsFunc domain smaller graph := by
  refine ⟨?_, function.2⟩
  intro pair member
  obtain ⟨x, hx, y, _, same⟩ := ZFSet.mem_prod.mp (function.1 member)
  subst pair
  exact ZFSet.mem_prod.mpr ⟨x, hx, y, bounded x y member, rfl⟩

namespace ModelStage

/-- A genuine set in M coding this particular bounded map. Functionality
excludes junk pairs and non-pairs; every source element has its actual value. -/
def RepresentsBoundedMap (stage : ModelStage.{u}) {alpha beta : Ordinal.{u}}
    (graph : stage.model.Element) (k : stage.BoundedMap alpha beta) : Prop :=
  ZFSet.IsFunc (stage.hierarchy (Order.succ alpha)).val
    (stage.hierarchy (Order.succ beta)).val graph.val ∧
  ∀ x, ZFSet.pair x.val (k x).val ∈ graph.val

namespace RepresentsBoundedMap
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}} {graph : stage.model.Element}
  {k : stage.BoundedMap alpha beta}

theorem congr_val (h : stage.RepresentsBoundedMap graph k) {l : stage.BoundedMap alpha beta}
    (same : ∀ x, (k x).val = (l x).val) : stage.RepresentsBoundedMap graph l := by
  refine ⟨h.1, ?_⟩
  intro x
  rw [← same x]
  exact h.2 x

theorem applies_iff (h : stage.RepresentsBoundedMap graph k)
    (x : stage.model.RankElement (Order.succ alpha)) (y : stage.model.RankElement (Order.succ beta)) :
    ZFSet.pair x.val y.val ∈ graph.val ↔ k x = y := by
  constructor
  · intro hedge
    have sourceMem := (stage.mem_hierarchy _ x.val).mpr x.property
    exact Subtype.ext ((h.1.2 x.val sourceMem).unique (h.2 x) hedge)
  · intro same
    rw [← same]
    exact h.2 x

theorem graph_exact (h : stage.RepresentsBoundedMap graph k) (a b : ZFSet.{u}) :
    ZFSet.pair a b ∈ graph.val ↔
      ∃ x : stage.model.RankElement (Order.succ alpha), x.val = a ∧ (k x).val = b := by
  constructor
  · intro hedge
    obtain ⟨ha, hb⟩ := ZFSet.pair_mem_prod.mp (h.1.1 hedge)
    let x : stage.model.RankElement (Order.succ alpha) := ⟨a, (stage.mem_hierarchy _ a).mp ha⟩
    let y : stage.model.RankElement (Order.succ beta) := ⟨b, (stage.mem_hierarchy _ b).mp hb⟩
    exact ⟨x, rfl, congrArg (fun z : stage.model.RankElement (Order.succ beta) => z.val)
      ((h.applies_iff x y).mp hedge)⟩
  · rintro ⟨x, rfl, rfl⟩
    exact h.2 x

theorem of_internalGraphElementary
    (h : stage.InternalGraphElementary alpha beta graph) :
    stage.RepresentsBoundedMap graph h.toRankEmbedding :=
  ⟨(stage.model.function_absolute _ _ _).mp h.1,
    fun x => (stage.model.graphApplies_absolute _ _ _).mp (h.value_applies x)⟩

/-- Recognition of a genuine set graph as a full internal elementary graph. -/
theorem toInternalGraphElementary (h : stage.RepresentsBoundedMap graph k) :
    stage.InternalGraphElementary alpha beta graph := by
  let embedding := (stage.rankDomainEquiv (Order.succ beta)).toElementaryEmbedding.comp
    (k.comp (stage.rankDomainEquiv (Order.succ alpha)).symm.toElementaryEmbedding)
  apply TransitiveClass.GraphElementary.of_embedding
    ((stage.model.function_absolute _ _ _).mpr h.1) embedding
  intro x y
  rw [stage.model.graphApplies_absolute]
  constructor
  · intro hedge
    apply Subtype.ext
    exact congrArg (fun z : stage.model.RankElement (Order.succ beta) => z.val)
      ((h.applies_iff ((stage.rankDomainEquiv (Order.succ alpha)).symm x)
        ((stage.rankDomainEquiv (Order.succ beta)).symm y)).mp hedge)
  · intro same
    have values := congrArg (fun z : SetDomain (stage.hierarchy (Order.succ beta)).val => z.val) same
    have edge := h.2 ((stage.rankDomainEquiv (Order.succ alpha)).symm x)
    change ZFSet.pair x.val (k ((stage.rankDomainEquiv (Order.succ alpha)).symm x)).val ∈ graph.val at edge
    change (k ((stage.rankDomainEquiv (Order.succ alpha)).symm x)).val = y.val at values
    rwa [values] at edge

end RepresentsBoundedMap
end ModelStage
end IBLP
