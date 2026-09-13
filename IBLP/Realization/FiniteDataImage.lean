import IBLP.Realization.BoundedRealization
import IBLP.Model.InternalGraphImage
import IBLP.Model.WeakAgreementImage

namespace IBLP
open FullMarkedBLP
universe u

namespace FiniteBoundedData
variable {source : ModelStage.{u}} {a : Pattern}

/-- Transport all actual finite point and row-graph data by an existing
elementary map. This theorem does not construct that map or transport marks. -/
noncomputable def image (D : FiniteBoundedData source a) (target : ModelStage.{u})
    (j : source.model.ElementaryMap target.model) : FiniteBoundedData target a where
  theta := fun i => source.ordinalImage j (D.theta i)
  increasing := (source.ordinalImage_strictMono j).comp D.increasing
  inaccessible := by
    intro i
    have same : j (source.ordinal (D.theta i)) = target.ordinal (source.ordinalImage j (D.theta i)) :=
      Subtype.ext (source.ordinalImage_compat j _)
    rw [← same]
    exact (j.internalInaccessible_iff _).mpr (D.inaccessible i)
  valid := D.valid
  shapes := D.shapes
  graph := fun r => j (D.graph r)
  elementary := fun r =>
    (source.internalGraphElementary_image target j _ _ _).mpr (D.elementary r)
  critical := fun r row minimum hr hm =>
    (source.graphCriticalPoint_image target j _ _).mpr (D.critical r row minimum hr hm)
  edges := by
    intro r row hr edge he
    have old := (source.model.graphApplies_absolute (D.graph r)
      (source.ordinal (D.point edge.1)) (source.ordinal (D.point edge.2))).mpr
      (D.edges r row hr edge he)
    have transported := (target.model.graphApplies_absolute _ _ _).mp
      ((j.graphApplies_iff _ _ _).mpr old)
    simpa only [source.ordinalImage_compat] using transported

theorem image_point (D : FiniteBoundedData source a) (target : ModelStage.{u})
    (j : source.model.ElementaryMap target.model) (i : Nat) :
    (D.image target j).point i = source.ordinalImage j (D.point i) := rfl

theorem image_top (D : FiniteBoundedData source a) (target : ModelStage.{u})
    (j : source.model.ElementaryMap target.model) :
    (D.image target j).top = source.ordinalImage j D.top := rfl

end FiniteBoundedData
end IBLP
