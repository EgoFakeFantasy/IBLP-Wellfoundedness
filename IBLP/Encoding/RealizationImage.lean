import IBLP.Encoding.RealizationCode
import IBLP.Encoding.FiniteImage
import IBLP.Realization.FiniteDataImage

namespace IBLP
open FullMarkedBLP
universe u

namespace FiniteBoundedData
variable {source : ModelStage.{u}} {a : Pattern}

theorem thetaCode_image (D : FiniteBoundedData source a) (target : ModelStage.{u})
    (j : source.model.ElementaryMap target.model) :
    j D.thetaCode = (D.image target j).thetaCode := by
  rw [thetaCode, source.finiteGraph_image]
  change target.finiteGraph (fun i => j (source.ordinal (D.theta i))) =
    target.finiteGraph (fun i => target.ordinal (source.ordinalImage j (D.theta i)))
  congr 1
  funext i
  exact Subtype.ext (source.ordinalImage_compat j _)

theorem graphsCode_image (D : FiniteBoundedData source a) (target : ModelStage.{u})
    (j : source.model.ElementaryMap target.model) :
    j D.graphsCode = (D.image target j).graphsCode := by
  rw [graphsCode, source.finiteGraph_image]
  rfl

/-- An existing elementary map transports the single stored set to precisely
the code of the transported finite data, retaining the fixed original pattern. -/
theorem code_image (D : FiniteBoundedData source a) (target : ModelStage.{u})
    (j : source.model.ElementaryMap target.model) :
    j D.code = (D.image target j).code := by
  simp only [code, source.orderedPair_image, source.patternCode_image,
    D.thetaCode_image, D.graphsCode_image]

end FiniteBoundedData
end IBLP
