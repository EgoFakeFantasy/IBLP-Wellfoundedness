import IBLP.Model.BoundedComposition
import IBLP.Rank.PrefixBounds

namespace IBLP
open FullMarkedBLP
universe u

namespace ModelStage

theorem weakAction_restriction (stage : ModelStage.{u}) {alpha beta delta epsilon : Ordinal.{u}}
    (k : stage.BoundedMap alpha beta) (small : stage.BoundedMap delta epsilon) (h : delta ≤ alpha)
    (agree : ∀ x, (small x).val = (k (stage.rankLift (Order.succ_le_succ h) x)).val)
    (z : stage.model.Element) :
    stage.weakAction small z = stage.weakAction k (stage.cutSpace.cut delta z) := by
  apply Subtype.ext
  have point := stage.weakAction_on_domain k (stage.rankLift (Order.succ_le_succ h) (stage.rankCut delta z))
  exact (agree (stage.rankCut delta z)).trans
    (congrArg (fun w : stage.model.Element => w.val) point.symm)

theorem rho_restriction (stage : ModelStage.{u}) {alpha beta delta epsilon : Ordinal.{u}}
    (k : stage.BoundedMap alpha beta) (small : stage.BoundedMap delta epsilon) (h : delta ≤ alpha)
    (agree : ∀ x, (small x).val = (k (stage.rankLift (Order.succ_le_succ h) x)).val)
    (eta : Ordinal.{u}) : stage.rho small eta = stage.rho k (min delta eta) := by
  have point : stage.rankLift (Order.succ_le_succ h) (stage.rankOrdinal (clippedOrdinal delta eta)) =
      stage.rankOrdinal (clippedOrdinal alpha (min delta eta)) := by
    apply Subtype.ext
    simp only [rankLift, rankOrdinal, clippedOrdinal, min_eq_right ((min_le_left delta eta).trans h)]
  have same := congrArg ZFSet.rank (agree (stage.rankOrdinal (clippedOrdinal delta eta)))
  rw [point] at same
  exact same

theorem restriction_endpoint (stage : ModelStage.{u}) {alpha beta delta epsilon : Ordinal.{u}}
    (k : stage.BoundedMap alpha beta) (small : stage.BoundedMap delta epsilon) (h : delta ≤ alpha)
    (agree : ∀ x, (small x).val = (k (stage.rankLift (Order.succ_le_succ h) x)).val) :
    epsilon = stage.rho k delta := by
  have same := stage.rho_restriction k small h agree delta
  simpa only [stage.rho_of_source_le small (le_refl delta), min_self] using same

/-- Internal-model forms of (3.7)--(3.10) now follow for genuine restrictions. -/
theorem boundedCutAction_restriction (stage : ModelStage.{u}) {alpha beta delta epsilon : Ordinal.{u}}
    (ha : Order.IsSuccLimit alpha) (hd : Order.IsSuccLimit delta)
    (k : stage.BoundedMap alpha beta) (small : stage.BoundedMap delta epsilon) (h : delta ≤ alpha)
    (agree : ∀ x, (small x).val = (k (stage.rankLift (Order.succ_le_succ h) x)).val) :
    CutRestriction (stage.boundedCutAction hd small) (stage.boundedCutAction ha k) where
  bound_le := by
    change epsilon ≤ beta
    rw [stage.restriction_endpoint k small h agree]
    exact stage.rho_le k delta
  act_eq := by
    intro z
    change stage.weakAction small z = stage.cutSpace.cut epsilon (stage.weakAction k z)
    rw [stage.weakAction_restriction k small h agree, stage.weakAction_cut_commute ha,
      ← stage.restriction_endpoint k small h agree]
  rho_eq := by
    intro eta
    change stage.rho small eta = min (stage.rho k eta) epsilon
    rw [stage.rho_restriction k small h agree, stage.rho_min,
      ← stage.restriction_endpoint k small h agree, min_comm]

theorem boundedRestrict_cutRestriction (stage : ModelStage.{u}) {alpha beta delta : Ordinal.{u}}
    (ha : Order.IsSuccLimit alpha) (hd : Order.IsSuccLimit delta)
    (k : stage.BoundedMap alpha beta) (h : delta ≤ alpha) :
    CutRestriction (stage.boundedCutAction hd (stage.boundedRestrict ha k delta h))
      (stage.boundedCutAction ha k) :=
  stage.boundedCutAction_restriction ha hd k _ h (stage.boundedRestrict_val ha k delta h)

end ModelStage
end IBLP
