import IBLP.Extender.CriticalAction
import IBLP.Model.CutActionImage
import IBLP.Model.WeakActionAbsolute
import IBLP.Rank.WeakAgreement

namespace IBLP.Extender.InternalExtension
open FullMarkedBLP Derivation
universe u
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}} {D : Derivation stage alpha beta}
  (E : InternalExtension D)

/-- A retained action whose natural bound is at most the critical point
can replace its elementary image on every new input. Equality at the
critical point is allowed; the critical ordinal itself need not be fixed. -/
theorem low_image_allInputs (c : Ordinal.{u}) (hc : c ≤ alpha)
    (critical : stage.model.GraphCriticalPoint D.graph (stage.ordinal c))
    {F : CutAction stage.cutSpace} {G H : CutAction E.next.cutSpace}
    (image : CutAction.Image E.embedding (stage.ordinalImage E.embedding) F G)
    (retained : ∀ z, (F.act (E.toSource z)).val = (H.act z).val) (small : F.bound ≤ c) :
    CutAction.AllInputAgreement G H F.bound := by
  intro z
  have imageBound : F.bound ≤ G.bound := by rw [image.bound]; exact stage.ordinalImage_le E.embedding F.bound
  have cutoff : F.bound ≤ G.rho c := (le_min small imageBound).trans (G.inflationary c)
  have changeInput := congrArg (E.next.cutSpace.cut F.bound) (E.action_cut_critical c hc critical G z)
  simp only [E.next.cutSpace.cut_lower cutoff] at changeInput
  have outputSource : E.toSource (H.act z) = F.act (E.toSource z) := Subtype.ext (retained z).symm
  have changeOutput := congrArg (E.next.cutSpace.cut F.bound) (E.cut_critical_in_target c hc critical (H.act z))
  simp only [E.next.cutSpace.cut_lower small] at changeOutput
  calc
    E.next.cutSpace.cut F.bound (G.act z) =
        E.next.cutSpace.cut F.bound (G.act (E.embedding (E.toSource z))) := changeInput.symm
    _ = E.next.cutSpace.cut F.bound (E.embedding (F.act (E.toSource z))) := congrArg _ (image.act _)
    _ = E.next.cutSpace.cut F.bound (E.embedding (E.toSource (H.act z))) := by rw [outputSource]
    _ = E.next.cutSpace.cut F.bound (H.act z) := changeOutput

theorem low_graph_image_allInputs (c : Ordinal.{u}) (hc : c ≤ alpha)
    (critical : stage.model.GraphCriticalPoint D.graph (stage.ordinal c))
    {rho sigma : Ordinal.{u}} (limit : Order.IsSuccLimit rho)
    {graph : stage.model.Element} {graph' : E.next.model.Element}
    (old : stage.InternalGraphElementary rho sigma graph)
    (retained : E.next.InternalGraphElementary rho sigma graph') (same : graph.val = graph'.val)
    (small : sigma ≤ c) :
    CutAction.AllInputAgreement
      (E.next.boundedCutAction (stage.ordinalImage_isSuccLimit E.next E.embedding rho limit)
        ((stage.internalGraphElementary_image E.next E.embedding rho sigma graph).mpr old).toRankEmbedding)
      (E.next.boundedCutAction limit retained.toRankEmbedding) sigma := by
  exact E.low_image_allInputs c hc critical (H := E.next.boundedCutAction limit retained.toRankEmbedding)
    (stage.boundedCutAction_image E.next E.embedding rho sigma limit graph old)
    (fun z => ModelStage.weakAction_absolute old retained same (E.toSource z) z rfl) small

end IBLP.Extender.InternalExtension
