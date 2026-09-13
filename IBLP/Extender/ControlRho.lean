import IBLP.Extender.ControlBridge
import IBLP.Model.AgreementOrdinals

namespace IBLP.Extender.InternalExtension
open FullMarkedBLP Derivation
universe u
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}} {D : Derivation stage alpha beta}
  (E : InternalExtension D)

theorem control_rho_eq_min (eta : Ordinal.{u}) :
    stage.rho D.map eta = min beta (stage.ordinalImage E.embedding eta) := by
  have values := E.cut_embedding (stage.ordinal eta)
  have image : E.embedding (stage.ordinal eta) = E.next.ordinal (stage.ordinalImage E.embedding eta) :=
    Subtype.ext (stage.ordinalImage_compat E.embedding eta)
  rw [image, ← E.next.cutSpace_cut, E.next.cutSpace_ordinal, stage.weakAction_ordinal] at values
  exact (Ordinal.toZFSet_injective values).symm

theorem control_rho_le_image (eta : Ordinal.{u}) :
    stage.rho D.map eta ≤ stage.ordinalImage E.embedding eta :=
  (E.control_rho_eq_min eta).trans_le (min_le_right _ _)

end IBLP.Extender.InternalExtension
