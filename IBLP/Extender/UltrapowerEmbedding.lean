import IBLP.Extender.UltrapowerFormula
import IBLP.Extender.ConstantRepresentative

namespace IBLP.Extender.UltrapowerAt
open FullMarkedBLP FirstOrder Language Derivation
universe u
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}
  (D : Derivation stage alpha beta) (seed : Seed stage beta)

/-- The constant-function embedding into the actual fixed-seed quotient. -/
noncomputable def constantEmbedding :
    ElementaryEmbedding membershipLanguage stage.model.Element (UltrapowerAt D seed) where
  toFun := fun x => mk D seed (Representative.constant x)
  map_formula' := by
    intro n phi values
    have h := los_formula D seed phi (Representative.constant ∘ values)
    rw [D.holds_constant_iff, stage.model.realize_atom, Function.comp_id] at h
    exact h

theorem constantEmbedding_mk (x : stage.model.Element) :
    constantEmbedding D seed x = mk D seed (Representative.constant x) := rfl

theorem constantEmbedding_injective : Function.Injective (constantEmbedding D seed) :=
  (constantEmbedding D seed).injective

end IBLP.Extender.UltrapowerAt
