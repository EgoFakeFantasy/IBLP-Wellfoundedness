import IBLP.Extender.RetainedGraph
import IBLP.Model.InaccessibleAbsolute

namespace IBLP
open FullMarkedBLP
universe u

theorem TransitiveClass.internalInaccessible_carrier_eq (M N : TransitiveClass.{u})
    (same : M.carrier = N.carrier) (k : M.Element) (l : N.Element) (values : k.val = l.val) :
    M.InternalInaccessible k ↔ N.InternalInaccessible l := by
  have models : M = N := by
    cases M
    cases N
    cases same
    rfl
  subst N
  have points : k = l := Subtype.ext values
  subst l
  rfl

namespace Extender.InternalExtension
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}} {D : Derivation stage alpha beta}
  (E : InternalExtension D)

/-- Every old point below the extension endpoint retains its full internal
inaccessibility. All witness ranks fit in the common limit rank segment. -/
theorem retained_inaccessible_iff (hb : Order.IsSuccLimit beta) (rho : Ordinal.{u})
    (below : rho < beta) :
    E.next.model.InternalInaccessible (E.next.ordinal rho) ↔
      stage.model.InternalInaccessible (stage.ordinal rho) := by
  let old : stage.model.RankElement beta := ⟨rho.toZFSet,
    stage.ordinalComplete rho, by simpa only [Ordinal.rank_toZFSet] using below⟩
  let new : E.next.model.RankElement beta := ⟨rho.toZFSet,
    E.next.ordinalComplete rho, by simpa only [Ordinal.rank_toZFSet] using below⟩
  exact (E.next.model.internalInaccessible_rankPart_iff hb new).symm.trans
    (((E.next.model.rankPart beta).internalInaccessible_carrier_eq
      (stage.model.rankPart beta) E.rankAgreement new old rfl).trans
        (stage.model.internalInaccessible_rankPart_iff hb old))

end Extender.InternalExtension
end IBLP
