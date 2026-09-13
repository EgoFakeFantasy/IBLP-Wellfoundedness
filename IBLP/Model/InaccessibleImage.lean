import IBLP.Model.InaccessibleAmbient
import IBLP.Model.InternalRho

namespace IBLP
open FullMarkedBLP
universe u

namespace ModelStage

theorem boundedMap_target_isSuccLimit (stage : ModelStage.{u}) {alpha beta : Ordinal.{u}}
    (k : stage.BoundedMap alpha beta) (sourceLimit : Order.IsSuccLimit alpha) :
    Order.IsSuccLimit beta := by
  let a := stage.rankOrdinal (endpoint alpha)
  have image : k a = stage.rankOrdinal (endpoint beta) := by
    rw [← stage.rankOrdinalAction_element k (endpoint alpha), stage.boundedMap_endpoint]
  have h := k.map_formula rankNonzeroLimitFormula ![a]
  have tuple : k ∘ ![a] = ![k a] := by funext i; fin_cases i; rfl
  rw [tuple, (stage.model.rankPart (Order.succ alpha)).nonzeroLimitFormula_absolute,
    (stage.model.rankPart (Order.succ beta)).nonzeroLimitFormula_absolute, image] at h
  exact (setNonzeroLimit_ordinal_iff beta).mp
    (h.mpr ((setNonzeroLimit_ordinal_iff alpha).mpr sourceLimit))

/-- The endpoint itself is covered using the sharp rank <= endpoint graph
bound. This closes the inaccessibility of a trace's genuine final codomain. -/
theorem boundedMap_endpoint_internalInaccessible (stage : ModelStage.{u})
    {alpha beta : Ordinal.{u}} (k : stage.BoundedMap alpha beta)
    (source : stage.model.InternalInaccessible (stage.ordinal alpha)) :
    stage.model.InternalInaccessible (stage.ordinal beta) := by
  have sourceLimit : Order.IsSuccLimit alpha := by
    simpa only [ModelStage.ordinal, Ordinal.rank_toZFSet] using
      stage.internalInaccessible_isSuccLimit (stage.ordinal alpha) source
  have targetLimit := stage.boundedMap_target_isSuccLimit k sourceLimit
  let a := stage.rankOrdinal (endpoint alpha)
  let b := stage.rankOrdinal (endpoint beta)
  have image : k a = b := by
    rw [← stage.rankOrdinalAction_element k (endpoint alpha), stage.boundedMap_endpoint]
  have sourceBound : a.val.rank ≤ alpha := by simp only [a, rankOrdinal_val, endpoint, Ordinal.rank_toZFSet, le_refl]
  have targetBound : b.val.rank ≤ beta := by simp only [b, rankOrdinal_val, endpoint, Ordinal.rank_toZFSet, le_refl]
  have sourceInCut := (stage.model.internalInaccessible_rankPart_endpoint_iff
    sourceLimit a sourceBound).mpr source
  have targetInCut := (k.internalInaccessible_iff a).mpr sourceInCut
  rw [image] at targetInCut
  exact (stage.model.internalInaccessible_rankPart_endpoint_iff targetLimit b targetBound).mp targetInCut

/-- Below the source endpoint use rank absoluteness and elementarity. At or
above the endpoint the clipped image is beta, whose inaccessibility is supplied
by the existing row endpoint invariant. No top-point absoluteness is asserted. -/
theorem rho_internalInaccessible (stage : ModelStage.{u}) {alpha beta : Ordinal.{u}}
    (k : stage.BoundedMap alpha beta) (sourceLimit : Order.IsSuccLimit alpha)
    (targetLimit : Order.IsSuccLimit beta)
    (targetInaccessible : stage.model.InternalInaccessible (stage.ordinal beta))
    (eta : Ordinal.{u}) (inaccessible : stage.model.InternalInaccessible (stage.ordinal eta)) :
    stage.model.InternalInaccessible (stage.ordinal (stage.rho k eta)) := by
  by_cases top : alpha ≤ eta
  · rw [stage.rho_of_source_le k top]
    exact targetInaccessible
  · have below : eta < alpha := lt_of_not_ge top
    have sourceRank : (stage.rankOrdinal (clippedOrdinal alpha eta)).val.rank < alpha := by
      simpa only [stage.rankOrdinal_val, Ordinal.rank_toZFSet, clippedOrdinal,
        min_eq_right below.le] using below
    have targetRank : (k (stage.rankOrdinal (clippedOrdinal alpha eta))).val.rank < beta := by
      have h := stage.rho_strictMonoOn k below.le (le_refl alpha) below
      rw [stage.rho_of_source_le k (le_refl alpha)] at h
      exact h
    have sourceEq : stage.model.inaccessibleRankInclude
        (stage.rankOrdinal (clippedOrdinal alpha eta)) = stage.ordinal eta := by
      apply Subtype.ext
      simp only [TransitiveClass.inaccessibleRankInclude, stage.rankOrdinal_val,
        clippedOrdinal, min_eq_right below.le, ModelStage.ordinal]
    have targetEq : stage.model.inaccessibleRankInclude
        (k (stage.rankOrdinal (clippedOrdinal alpha eta))) = stage.ordinal (stage.rho k eta) := by
      apply Subtype.ext
      exact stage.rankOrdinalAction_compat k (clippedOrdinal alpha eta)
    have h := TransitiveClass.successorRankMap_internalInaccessible_iff
      sourceLimit targetLimit k (stage.rankOrdinal (clippedOrdinal alpha eta)) sourceRank targetRank
    rw [sourceEq, targetEq] at h
    exact h.mpr inaccessible

end ModelStage
end IBLP
