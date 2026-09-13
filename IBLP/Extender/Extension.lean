import IBLP.Extender.Internality
import IBLP.Extender.RankAgreement
import IBLP.Extender.TupleSystem
import IBLP.Model.GraphCriticalPoint

namespace IBLP.Extender
open FullMarkedBLP Derivation
universe u

/-- The complete model-level output used in finite repetitions of
manuscript Lemma 4.1. The next stage includes full external countable closure. -/
structure InternalExtension {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}
    (D : Derivation stage alpha beta) where
  next : ModelStage.{u}
  embedding : stage.model.ElementaryMap next.model
  inside : next.model.carrier ⊆ stage.model.carrier
  agreement : ∀ x : Test stage alpha, (embedding (stage.rankInclude _ x)).val = (D.map x).val
  endpoint : (embedding (stage.ordinal alpha)).val = beta.toZFSet
  rankAgreement : (next.model.rankPart beta).carrier = (stage.model.rankPart beta).carrier

noncomputable def Derivation.extend {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}
    (D : Derivation stage alpha beta) (ha : Order.IsSuccLimit alpha) (hb : Order.IsSuccLimit beta)
    (inaccessible : stage.model.InternalInaccessible (stage.ordinal beta)) : InternalExtension D where
  next := Ultrapower.nextStage D ha hb inaccessible
  embedding := Ultrapower.embedding D ha hb inaccessible
  inside := Ultrapower.target_subset D ha hb inaccessible
  agreement := Ultrapower.embedding_agrees D ha hb inaccessible
  endpoint := Ultrapower.embedding_endpoint D ha hb inaccessible
  rankAgreement := Ultrapower.rankPart_agrees D ha hb inaccessible

namespace InternalExtension
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}} {D : Derivation stage alpha beta}
  (E : InternalExtension D)

theorem countablyClosed : E.next.model.CountablyClosed := E.next.countablyClosed

theorem rank_mem_iff (x : ZFSet.{u}) (hx : x.rank < beta) :
    x ∈ E.next.model.carrier ↔ x ∈ stage.model.carrier := by
  have h : (x ∈ E.next.model.carrier ∧ x.rank < beta) ↔ (x ∈ stage.model.carrier ∧ x.rank < beta) := by
    change x ∈ (E.next.model.rankPart beta).carrier ↔ x ∈ (stage.model.rankPart beta).carrier
    rw [E.rankAgreement]
  simpa only [hx, and_true] using h

/-- The saved graph's exact critical point remains the least moved ordinal
of the full embedding. No new critical-point assumption is introduced. -/
theorem critical_agrees (c : Ordinal.{u}) (hc : c ≤ alpha)
    (critical : stage.model.GraphCriticalPoint D.graph (stage.ordinal c)) :
    (E.embedding (stage.ordinal c)).val ≠ c.toZFSet ∧
      ∀ a : Ordinal.{u}, a < c → (E.embedding (stage.ordinal a)).val = a.toZFSet := by
  obtain ⟨moved, fixed⟩ := (stage.graphCriticalPoint_iff_boundedMap D.represents c hc).mp critical
  constructor
  · have same := E.agreement (stage.rankOrdinal ⟨c, Order.lt_succ_of_le hc⟩)
    exact fun h => moved (same.symm.trans h)
  · intro a ha
    have same := E.agreement (stage.rankOrdinal ⟨a, Order.lt_succ_of_le (ha.le.trans hc)⟩)
    exact same.trans (fixed a ha)

end InternalExtension
end IBLP.Extender
