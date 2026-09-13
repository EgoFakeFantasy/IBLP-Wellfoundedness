import IBLP.Model.WeakAgreementFormula
import IBLP.Model.GraphCriticalPoint
import IBLP.Model.HierarchyImage

namespace IBLP
open FullMarkedBLP
universe u

namespace ModelStage

theorem graphWeakAgreement_image (source target : ModelStage.{u})
    (j : source.model.ElementaryMap target.model)
    (f g : source.model.Element) (alpha gamma delta : Ordinal.{u}) :
    target.model.GraphWeakAgreement (j f) (j g)
      (target.hierarchy (source.ordinalImage j alpha))
      (target.hierarchy (source.ordinalImage j gamma))
      (target.hierarchy (source.ordinalImage j delta)) ↔
    source.model.GraphWeakAgreement f g (source.hierarchy alpha)
      (source.hierarchy gamma) (source.hierarchy delta) := by
  rw [← source.hierarchy_image target j alpha, ← source.hierarchy_image target j gamma,
    ← source.hierarchy_image target j delta]
  exact j.graphWeakAgreement_iff _ _ _ _ _

theorem graphCriticalPoint_image (source target : ModelStage.{u})
    (j : source.model.ElementaryMap target.model) (graph : source.model.Element)
    (c : Ordinal.{u}) :
    target.model.GraphCriticalPoint (j graph) (target.ordinal (source.ordinalImage j c)) ↔
      source.model.GraphCriticalPoint graph (source.ordinal c) := by
  have same : j (source.ordinal c) = target.ordinal (source.ordinalImage j c) :=
    Subtype.ext (source.ordinalImage_compat j c)
  rw [← same]
  exact j.graphCriticalPoint_iff _ _

end ModelStage
end IBLP
