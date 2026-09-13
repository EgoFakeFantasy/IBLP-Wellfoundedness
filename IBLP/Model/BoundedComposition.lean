import IBLP.Model.BoundedRestriction

namespace IBLP
open FullMarkedBLP
universe u

namespace ModelStage

/-- Before composing, restrict the outer map to the inner map's entire
target successor rank. This is the ordinary elementary composite in (3.12). -/
noncomputable def compatibleCompose (stage : ModelStage.{u}) {alpha beta gamma delta : Ordinal.{u}}
    (ha : Order.IsSuccLimit alpha) (k : stage.BoundedMap alpha beta)
    (l : stage.BoundedMap gamma delta) (h : delta ≤ alpha) :
    stage.BoundedMap gamma (stage.rho k delta) := (stage.boundedRestrict ha k delta h).comp l

theorem compatibleCompose_val (stage : ModelStage.{u}) {alpha beta gamma delta : Ordinal.{u}}
    (ha : Order.IsSuccLimit alpha) (k : stage.BoundedMap alpha beta)
    (l : stage.BoundedMap gamma delta) (h : delta ≤ alpha)
    (x : stage.model.RankElement (Order.succ gamma)) :
    (stage.compatibleCompose ha k l h x).val =
      (k (stage.rankLift (Order.succ_le_succ h) (l x))).val :=
  stage.boundedRestrict_val ha k delta h (l x)

theorem compatibleCompose_weakAction (stage : ModelStage.{u}) {alpha beta gamma delta : Ordinal.{u}}
    (ha : Order.IsSuccLimit alpha) (k : stage.BoundedMap alpha beta)
    (l : stage.BoundedMap gamma delta) (h : delta ≤ alpha) (z : stage.model.Element) :
    stage.weakAction (stage.compatibleCompose ha k l h) z =
      stage.weakAction k (stage.weakAction l z) := by
  apply Subtype.ext
  have point := stage.weakAction_on_domain k
    (stage.rankLift (Order.succ_le_succ h) (l (stage.rankCut gamma z)))
  calc
    (stage.weakAction (stage.compatibleCompose ha k l h) z).val =
        (k (stage.rankLift (Order.succ_le_succ h) (l (stage.rankCut gamma z)))).val :=
      stage.compatibleCompose_val ha k l h _
    _ = (stage.weakAction k (stage.weakAction l z)).val :=
      congrArg (fun w : stage.model.Element => w.val) point.symm

theorem compatibleCompose_rho (stage : ModelStage.{u}) {alpha beta gamma delta : Ordinal.{u}}
    (ha : Order.IsSuccLimit alpha) (k : stage.BoundedMap alpha beta)
    (l : stage.BoundedMap gamma delta) (h : delta ≤ alpha) (eta : Ordinal.{u}) :
    stage.rho (stage.compatibleCompose ha k l h) eta = stage.rho k (stage.rho l eta) := by
  have same := stage.compatibleCompose_weakAction ha k l h (stage.ordinal eta)
  rw [stage.weakAction_ordinal, stage.weakAction_ordinal, stage.weakAction_ordinal] at same
  simpa only [ordinal, Ordinal.rank_toZFSet] using
    congrArg (fun w : stage.model.Element => w.val.rank) same

end ModelStage
end IBLP
