import IBLP.Extender.ControlBridge
import IBLP.Rank.WordImage

namespace IBLP.Extender.InternalExtension
open FullMarkedBLP Derivation
universe u
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}} {D : Derivation stage alpha beta}
  (E : InternalExtension D)

theorem image_cut_eq {delta : Ordinal.{u}} {x y : stage.model.Element}
    (same : stage.cutSpace.cut delta x = stage.cutSpace.cut delta y) :
    E.next.cutSpace.cut (stage.ordinalImage E.embedding delta) (E.embedding x) =
      E.next.cutSpace.cut (stage.ordinalImage E.embedding delta) (E.embedding y) := by
  have mapped := congrArg E.embedding same
  rw [stage.cutSpace_cut, stage.cutSpace_cut, stage.cut_image, stage.cut_image] at mapped
  simpa only [E.next.cutSpace_cut] using mapped

/-- Manuscript (5.5)--(5.6) on all inputs: critical input replacement,
the image of the old relation, and the actual control bridge supply the
three separately stated bounds. The numerical natural-bound estimates
are deliberately left for the concrete copied arrays. -/
theorem high_crossing_allInputs (ha : Order.IsSuccLimit alpha) (c : Ordinal.{u}) (hc : c ≤ alpha)
    (critical : stage.model.GraphCriticalPoint D.graph (stage.ordinal c))
    {delta tau cutoff : Ordinal.{u}} (tauBound : tau ≤ beta)
    {F U T V : CutAction stage.cutSpace} {F' U' T' V' : CutAction E.next.cutSpace}
    (old : CutAction.AllInputAgreement F (U.comp V) delta)
    (imageF : CutAction.Image E.embedding (stage.ordinalImage E.embedding) F F')
    (imageU : CutAction.Image E.embedding (stage.ordinalImage E.embedding) U U')
    (control : CutAction.AllInputAgreement (stage.boundedCutAction ha D.map) T tau)
    (retainedT : ∀ z, (T.act (E.toSource z)).val = (T'.act z).val)
    (retainedV : ∀ z, (V.act (E.toSource z)).val = (V'.act z).val)
    (inputBound : cutoff ≤ F'.rho c) (oldBound : cutoff ≤ stage.ordinalImage E.embedding delta)
    (bridgeBound : cutoff ≤ U'.rho tau) :
    CutAction.AllInputAgreement F' (U'.comp (T'.comp V')) cutoff := by
  intro z
  have input := congrArg (E.next.cutSpace.cut cutoff) (E.action_cut_critical c hc critical F' z)
  simp only [E.next.cutSpace.cut_lower inputBound] at input
  have copied := E.image_cut_eq (old (E.toSource z))
  change E.next.cutSpace.cut (stage.ordinalImage E.embedding delta) (E.embedding (F.act (E.toSource z))) =
    E.next.cutSpace.cut (stage.ordinalImage E.embedding delta) (E.embedding (U.act (V.act (E.toSource z)))) at copied
  rw [← imageF.act, ← imageU.act] at copied
  have relation := congrArg (E.next.cutSpace.cut cutoff) copied
  simp only [E.next.cutSpace.cut_lower oldBound] at relation
  have bridge := congrArg U'.act (E.control_bridge ha tauBound control retainedT retainedV z)
  simp only [U'.cut_commute] at bridge
  have restrictedBridge := congrArg (E.next.cutSpace.cut cutoff) bridge
  simp only [E.next.cutSpace.cut_lower bridgeBound] at restrictedBridge
  exact input.symm.trans (relation.trans restrictedBridge)

/-- The boundary may already be the mark itself, leaving no copied initial
factor. This case uses the control cutoff directly and needs no fictitious
nonempty word for an empty prefix. -/
theorem high_crossing_no_front (ha : Order.IsSuccLimit alpha) (c : Ordinal.{u}) (hc : c ≤ alpha)
    (critical : stage.model.GraphCriticalPoint D.graph (stage.ordinal c))
    {delta tau cutoff : Ordinal.{u}} (tauBound : tau ≤ beta)
    {F T V : CutAction stage.cutSpace} {F' T' V' : CutAction E.next.cutSpace}
    (old : CutAction.AllInputAgreement F V delta)
    (imageF : CutAction.Image E.embedding (stage.ordinalImage E.embedding) F F')
    (control : CutAction.AllInputAgreement (stage.boundedCutAction ha D.map) T tau)
    (retainedT : ∀ z, (T.act (E.toSource z)).val = (T'.act z).val)
    (retainedV : ∀ z, (V.act (E.toSource z)).val = (V'.act z).val)
    (inputBound : cutoff ≤ F'.rho c) (oldBound : cutoff ≤ stage.ordinalImage E.embedding delta)
    (bridgeBound : cutoff ≤ tau) : CutAction.AllInputAgreement F' (T'.comp V') cutoff := by
  intro z
  have input := congrArg (E.next.cutSpace.cut cutoff) (E.action_cut_critical c hc critical F' z)
  simp only [E.next.cutSpace.cut_lower inputBound] at input
  have copied := E.image_cut_eq (old (E.toSource z))
  rw [← imageF.act] at copied
  have relation := congrArg (E.next.cutSpace.cut cutoff) copied
  simp only [E.next.cutSpace.cut_lower oldBound] at relation
  have bridge := congrArg (E.next.cutSpace.cut cutoff) (E.control_bridge ha tauBound control retainedT retainedV z)
  simp only [E.next.cutSpace.cut_lower bridgeBound] at bridge
  exact input.symm.trans (relation.trans bridge)

end IBLP.Extender.InternalExtension
