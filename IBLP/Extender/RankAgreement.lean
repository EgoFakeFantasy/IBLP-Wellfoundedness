import IBLP.Extender.BoundedAgreement

namespace IBLP.Extender.Ultrapower
open FullMarkedBLP Derivation
universe u
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}
  (D : Derivation stage alpha beta) (ha : Order.IsSuccLimit alpha) (hb : Order.IsSuccLimit beta)
  (inaccessible : stage.model.InternalInaccessible (stage.ordinal beta))

theorem embedding_endpoint :
    (embedding D ha hb inaccessible (stage.ordinal alpha)).val = beta.toZFSet := by
  have h := embedding_agrees D ha hb inaccessible (stage.rankOrdinal (endpoint alpha))
  rw [stage.rankOrdinalAction_compat, stage.boundedMap_endpoint] at h
  exact h

theorem ordinalImage_endpoint : stage.ordinalImage (embedding D ha hb inaccessible) alpha = beta := by
  change (embedding D ha hb inaccessible (stage.ordinal alpha)).val.rank = beta
  rw [embedding_endpoint, Ordinal.rank_toZFSet]

theorem embedding_top :
    (embedding D ha hb inaccessible (stage.hierarchy alpha)).val = (stage.hierarchy beta).val := by
  have h := embedding_agrees D ha hb inaccessible (stage.rankHierarchy (endpoint alpha))
  rw [stage.boundedMap_top] at h
  exact h

/-- The entire beta-th internal rank level agrees as an actual set. -/
theorem hierarchy_agrees :
    ((nextStage D ha hb inaccessible).hierarchy beta).val = (stage.hierarchy beta).val := by
  have h := stage.hierarchy_image (nextStage D ha hb inaccessible) (embedding D ha hb inaccessible) alpha
  have indexEq := congrArg (fun o => ((nextStage D ha hb inaccessible).hierarchy o).val)
    (ordinalImage_endpoint D ha hb inaccessible)
  exact indexEq.symm.trans ((congrArg Subtype.val h).symm.trans (embedding_top D ha hb inaccessible))

theorem rankPart_agrees :
    ((nextStage D ha hb inaccessible).model.rankPart beta).carrier = (stage.model.rankPart beta).carrier := by
  ext x
  change (x ∈ (nextStage D ha hb inaccessible).model.carrier ∧ x.rank < beta) ↔
    x ∈ stage.model.carrier ∧ x.rank < beta
  rw [← (nextStage D ha hb inaccessible).mem_hierarchy, ← stage.mem_hierarchy, hierarchy_agrees]

end IBLP.Extender.Ultrapower
