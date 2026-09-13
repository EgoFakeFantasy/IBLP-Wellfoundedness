import IBLP.Model.InternalWeakTruncation
import IBLP.Rank.WeakEdges

namespace IBLP.ModelStage
open FullMarkedBLP
universe u

theorem cutSpace_ordinal (stage : ModelStage.{u}) (delta eta : Ordinal.{u}) :
    stage.cutSpace.cut delta (stage.ordinal eta) = stage.ordinal (min delta eta) :=
  Subtype.ext (congrArg (fun x : stage.model.RankElement (Order.succ delta) => x.val)
    (stage.rankCut_ordinal delta eta))

/-- At the second action's natural bound, weak agreement identifies its
entire ordinal action as the clipped ordinal action of the first map. -/
theorem allInputAgreement_rho_min (stage : ModelStage.{u}) {F G : CutAction stage.cutSpace}
    (agreement : CutAction.AllInputAgreement F G G.bound)
    (ordF : ∀ eta, F.act (stage.ordinal eta) = stage.ordinal (F.rho eta))
    (ordG : ∀ eta, G.act (stage.ordinal eta) = stage.ordinal (G.rho eta)) (eta : Ordinal.{u}) :
    G.rho eta = min G.bound (F.rho eta) := by
  have values := agreement (stage.ordinal eta)
  rw [ordF, ordG, stage.cutSpace_ordinal, stage.cutSpace_ordinal, min_eq_right (G.rho_le_bound eta)] at values
  exact (Ordinal.toZFSet_injective (congrArg Subtype.val values)).symm

theorem allInputAgreement_rho_le (stage : ModelStage.{u}) {F G : CutAction stage.cutSpace}
    (agreement : CutAction.AllInputAgreement F G G.bound)
    (ordF : ∀ eta, F.act (stage.ordinal eta) = stage.ordinal (F.rho eta))
    (ordG : ∀ eta, G.act (stage.ordinal eta) = stage.ordinal (G.rho eta)) (eta : Ordinal.{u}) :
    G.rho eta ≤ F.rho eta :=
  (stage.allInputAgreement_rho_min agreement ordF ordG eta).trans_le (min_le_right _ _)

end IBLP.ModelStage
