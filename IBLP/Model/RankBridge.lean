import IBLP.Model.BoundedGraph
import IBLP.Model.HierarchyImage

namespace IBLP
open FullMarkedBLP FirstOrder Language
universe u

namespace ModelStage

/-- The internal hierarchy set and the model's actual rank cut carry exactly
the same membership structure, at every level including successor levels. -/
noncomputable def rankDomainEquiv (stage : ModelStage.{u}) (beta : Ordinal.{u}) :
    Language.Equiv membershipLanguage (stage.model.RankElement beta)
      (SetDomain (stage.hierarchy beta).val) where
  toFun := fun x => ⟨x.val, (stage.mem_hierarchy beta x.val).mpr x.property⟩
  invFun := fun x => ⟨x.val, (stage.mem_hierarchy beta x.val).mp x.property⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_fun' := fun f => Empty.elim f
  map_rel' := by
    intro n relation values
    obtain ⟨same⟩ := relation
    subst n
    rfl

@[simp] theorem rankDomainEquiv_val (stage : ModelStage.{u}) (beta : Ordinal.{u})
    (x : stage.model.RankElement beta) : (stage.rankDomainEquiv beta x).val = x.val := rfl

@[simp] theorem rankDomainEquiv_symm_val (stage : ModelStage.{u}) (beta : Ordinal.{u})
    (x : SetDomain (stage.hierarchy beta).val) : ((stage.rankDomainEquiv beta).symm x).val = x.val := rfl

/-- The inclusion retains actual model membership instead of replacing the
internal rank cut by the ambient universe's full rank. -/
def rankInclude (stage : ModelStage.{u}) (beta : Ordinal.{u}) :
    stage.model.RankElement beta → stage.model.Element := fun x => ⟨x.val, x.property.1⟩

@[simp] theorem setInclude_rankDomainEquiv (stage : ModelStage.{u}) (beta : Ordinal.{u})
    (x : stage.model.RankElement beta) :
    stage.model.setInclude (stage.hierarchy beta) (stage.rankDomainEquiv beta x) = stage.rankInclude beta x := rfl

/-- An actual internal graph between the successor rank levels used in IBLP. -/
def InternalGraphElementary (stage : ModelStage.{u}) (alpha beta : Ordinal.{u})
    (graph : stage.model.Element) : Prop :=
  stage.model.GraphElementary graph (stage.hierarchy (Order.succ alpha)) (stage.hierarchy (Order.succ beta))

namespace InternalGraphElementary

/-- The genuine elementary map recovered solely from the internal graph. -/
noncomputable def toRankEmbedding {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}
    {graph : stage.model.Element} (h : stage.InternalGraphElementary alpha beta graph) :
    (stage.model.rankPart (Order.succ alpha)).ElementaryMap (stage.model.rankPart (Order.succ beta)) :=
  (stage.rankDomainEquiv (Order.succ beta)).symm.toElementaryEmbedding.comp
    (h.toEmbedding.comp (stage.rankDomainEquiv (Order.succ alpha)).toElementaryEmbedding)

theorem toRankEmbedding_val {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}
    {graph : stage.model.Element} (h : stage.InternalGraphElementary alpha beta graph)
    (x : stage.model.RankElement (Order.succ alpha)) :
    (h.toRankEmbedding x).val = (h.toEmbedding (stage.rankDomainEquiv (Order.succ alpha) x)).val := rfl

theorem value_applies {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}
    {graph : stage.model.Element} (h : stage.InternalGraphElementary alpha beta graph)
    (x : stage.model.RankElement (Order.succ alpha)) :
    stage.model.GraphApplies graph (stage.rankInclude (Order.succ alpha) x)
      (stage.rankInclude (Order.succ beta) (h.toRankEmbedding x)) :=
  TransitiveClass.GraphElementary.value_applies h (stage.rankDomainEquiv (Order.succ alpha) x)

theorem applies_iff {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}
    {graph : stage.model.Element} (h : stage.InternalGraphElementary alpha beta graph)
    (x : stage.model.RankElement (Order.succ alpha)) (y : stage.model.RankElement (Order.succ beta)) :
    stage.model.GraphApplies graph (stage.rankInclude (Order.succ alpha) x)
      (stage.rankInclude (Order.succ beta) y) ↔ h.toRankEmbedding x = y := by
  constructor
  · intro hedge
    apply Subtype.ext
    exact congrArg (fun z : SetDomain (stage.hierarchy (Order.succ beta)).val => z.val)
      ((TransitiveClass.GraphElementary.applies_iff h (stage.rankDomainEquiv (Order.succ alpha) x)
        (stage.rankDomainEquiv (Order.succ beta) y)).mp hedge)
  · intro same
    rw [← same]
    exact h.value_applies x

theorem graph_exact {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}
    {graph : stage.model.Element} (h : stage.InternalGraphElementary alpha beta graph) (a b : ZFSet.{u}) :
    ZFSet.pair a b ∈ graph.val ↔
      ∃ x : stage.model.RankElement (Order.succ alpha), x.val = a ∧ (h.toRankEmbedding x).val = b := by
  rw [TransitiveClass.GraphElementary.graph_exact h]
  constructor
  · rintro ⟨x, hx, hy⟩
    exact ⟨(stage.rankDomainEquiv (Order.succ alpha)).symm x, hx, hy⟩
  · rintro ⟨x, hx, hy⟩
    exact ⟨stage.rankDomainEquiv (Order.succ alpha) x, hx, hy⟩

end InternalGraphElementary

/-- Image transport of an internal successor-rank graph. The displayed level
image equalities are explicit; no unproved successor preservation is hidden. -/
theorem internalGraphElementary_image_iff (source target : ModelStage.{u})
    (j : source.model.ElementaryMap target.model) (alpha beta alpha' beta' : Ordinal.{u})
    (graph : source.model.Element)
    (sourceLevel : source.ordinalImage j (Order.succ alpha) = Order.succ alpha')
    (targetLevel : source.ordinalImage j (Order.succ beta) = Order.succ beta') :
    target.InternalGraphElementary alpha' beta' (j graph) ↔ source.InternalGraphElementary alpha beta graph := by
  have domainImage := source.hierarchy_image target j (Order.succ alpha)
  have rangeImage := source.hierarchy_image target j (Order.succ beta)
  rw [sourceLevel] at domainImage
  rw [targetLevel] at rangeImage
  change target.model.GraphElementary (j graph) (target.hierarchy (Order.succ alpha'))
    (target.hierarchy (Order.succ beta')) ↔ _
  rw [← domainImage, ← rangeImage]
  exact j.graphElementary_iff graph _ _

end ModelStage
end IBLP
