import IBLP.Extender.UltrapowerEmbedding
import IBLP.Extender.FormulaPullback

namespace IBLP.Extender.UltrapowerAt
open FullMarkedBLP FirstOrder Language Derivation
universe u
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}
  (D : Derivation stage alpha beta) (seed : Seed stage beta)
  (p : IndexMap stage alpha)

/-- Pullback along an actual internal index graph induces a map from the
projected component to the original component. -/
noncomputable def transition : UltrapowerAt D (D.project p seed) → UltrapowerAt D seed :=
  fun x => Quotient.liftOn x (fun f => mk D seed (f.pullback p)) (by
    intro f g h
    exact (mk_eq_iff D seed _ _).mpr ((D.repEquivalent_pullback_iff seed p f g).mpr h))

theorem transition_mk (f : Representative stage alpha) :
    transition D seed p (mk D (D.project p seed) f) = mk D seed (f.pullback p) := rfl

/-- Every component transition is elementary for the native membership
language, with no elementarity assumption supplied as a field. -/
noncomputable def transitionEmbedding :
    ElementaryEmbedding membershipLanguage (UltrapowerAt D (D.project p seed)) (UltrapowerAt D seed) where
  toFun := transition D seed p
  map_formula' := by
    classical
    intro n phi values
    let fs : Fin n → Representative stage alpha :=
      fun i => Classical.choose (mk_surjective D (D.project p seed) (values i))
    have same : mk D (D.project p seed) ∘ fs = values :=
      funext (fun i => Classical.choose_spec (mk_surjective D (D.project p seed) (values i)))
    rw [← same]
    change phi.Realize (mk D seed ∘ (fun i => (fs i).pullback p)) ↔ _
    rw [los_formula, D.holds_pullback_iff, los_formula]

theorem transitionEmbedding_mk (f : Representative stage alpha) :
    transitionEmbedding D seed p (mk D (D.project p seed) f) = mk D seed (f.pullback p) := rfl

theorem transition_injective : Function.Injective (transition D seed p) :=
  (transitionEmbedding D seed p).injective

theorem transition_constant (x : stage.model.Element) :
    transition D seed p (constantEmbedding D (D.project p seed) x) = constantEmbedding D seed x := by
  apply (mk_eq_iff D seed _ _).mpr
  apply D.holds_of_pointwise
  intro z
  change ((Representative.constant x).pullback p).value z = (Representative.constant x).value z
  simp only [Representative.pullback_value, Representative.constant_value]

end IBLP.Extender.UltrapowerAt
