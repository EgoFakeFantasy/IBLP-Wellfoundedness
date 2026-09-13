import IBLP.Extender.CriticalAction
import IBLP.Rank.WeakAgreement
import IBLP.Model.InternalWeakTruncation

namespace IBLP.Extender.InternalExtension
open FullMarkedBLP Derivation
universe u
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}} {D : Derivation stage alpha beta}
  (E : InternalExtension D)

theorem cut_embedding_below {eta : Ordinal.{u}} (below : eta ≤ beta) (z : stage.model.Element) :
    (E.next.cutSpace.cut eta (E.embedding z)).val =
      (stage.cutSpace.cut eta (stage.weakAction D.map z)).val := by
  have exactValue := E.cut_embedding z
  rw [E.next.cut_val] at exactValue
  have restricted := congrArg (zfCutSpace.cut eta) exactValue
  change zfCutSpace.cut eta (zfCutSpace.cut beta (E.embedding z).val) = _ at restricted
  rw [zfCutSpace.cut_lower below] at restricted
  exact restricted

/-- The actual control-row weak certificate replaces the embedded old
suffix value by the retained control trace followed by the retained suffix. -/
theorem control_bridge (ha : Order.IsSuccLimit alpha) {tau : Ordinal.{u}} (below : tau ≤ beta)
    {T V : CutAction stage.cutSpace} {T' V' : CutAction E.next.cutSpace}
    (control : CutAction.AllInputAgreement (stage.boundedCutAction ha D.map) T tau)
    (retainedT : ∀ z, (T.act (E.toSource z)).val = (T'.act z).val)
    (retainedV : ∀ z, (V.act (E.toSource z)).val = (V'.act z).val)
    (z : E.next.model.Element) :
    E.next.cutSpace.cut tau (E.embedding (V.act (E.toSource z))) =
      E.next.cutSpace.cut tau (T'.act (V'.act z)) := by
  have sameV : E.toSource (V'.act z) = V.act (E.toSource z) := Subtype.ext (retainedV z).symm
  have sameT : (T.act (V.act (E.toSource z))).val = (T'.act (V'.act z)).val := by
    rw [← sameV]
    exact retainedT (V'.act z)
  apply Subtype.ext
  calc
    (E.next.cutSpace.cut tau (E.embedding (V.act (E.toSource z)))).val =
        (stage.cutSpace.cut tau (stage.weakAction D.map (V.act (E.toSource z)))).val := E.cut_embedding_below below _
    _ = (stage.cutSpace.cut tau (T.act (V.act (E.toSource z)))).val := congrArg Subtype.val (control _)
    _ = (E.next.cutSpace.cut tau (T'.act (V'.act z))).val := congrArg (zfCutSpace.cut tau) sameT

end IBLP.Extender.InternalExtension
