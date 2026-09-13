import IBLP.Extender.ModelChange
import IBLP.Rank.WordAction

namespace IBLP.Extender.InternalExtension
open FullMarkedBLP Derivation
universe u
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}} {D : Derivation stage alpha beta}
  (E : InternalExtension D)

def toSource (z : E.next.model.Element) : stage.model.Element := ⟨z.val, E.inside z.property⟩

theorem cut_critical_in_target (c : Ordinal.{u}) (hc : c ≤ alpha)
    (critical : stage.model.GraphCriticalPoint D.graph (stage.ordinal c)) (z : E.next.model.Element) :
    E.next.cutSpace.cut c (E.embedding (E.toSource z)) = E.next.cutSpace.cut c z := by
  rw [E.next.cutSpace_cut, E.next.cutSpace_cut]
  apply Subtype.ext
  rw [E.cut_critical c hc critical, stage.cut_val, E.next.cut_val]
  rfl

/-- Manuscript (5.2) for every cut action in N, hence also for every
nonempty finite word of actual bounded maps. -/
theorem action_cut_critical (c : Ordinal.{u}) (hc : c ≤ alpha)
    (critical : stage.model.GraphCriticalPoint D.graph (stage.ordinal c))
    (A : CutAction E.next.cutSpace) (z : E.next.model.Element) :
    E.next.cutSpace.cut (A.rho c) (A.act (E.embedding (E.toSource z))) =
      E.next.cutSpace.cut (A.rho c) (A.act z) := by
  have h := congrArg A.act (E.cut_critical_in_target c hc critical z)
  simpa only [A.cut_commute] using h

end IBLP.Extender.InternalExtension
