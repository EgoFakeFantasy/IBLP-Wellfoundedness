import IBLP.Realization.ExpandRealized

namespace IBLP
universe u

/-- The exact remaining finite-formula predicate: existence of a complete
realization of this fixed finite pattern with top below a given ordinal. -/
def RealizationBelow (stage : ModelStage.{u}) (a : Pattern) (bound : Ordinal.{u}) : Prop :=
  ∃ R : BoundedRealization stage a, R.top < bound

/-- Reflection of each fixed finite pattern's below-bound formula is
sufficient. A uniform object-language truth predicate over all patterns
or an object-language definition of external non-accessibility is not
assumed. This interface must still be proved from genuine finite formulas. -/
def ReflectsRealizationBelow (source : ModelStage.{u}) : Prop :=
  ∀ target : ModelStage.{u}, ∀ j : source.model.ElementaryMap target.model,
    ∀ a bound, RealizationBelow target a (source.ordinalImage j bound) → RealizationBelow source a bound

/-- The minimal bad top argument uses only the already proved original
expansion closure and reflection of the fixed child's complete realization
formula. The reflection interface is explicit and not an axiom. -/
theorem BoundedRealization.acc_of_below_reflection {stage : ModelStage.{u}} {a : Pattern}
    (R : BoundedRealization stage a) (reflects : ReflectsRealizationBelow stage) : Acc Child a := by
  classical
  by_contra bad
  let badTops : Set Ordinal.{u} := {bound | ∃ pattern, ¬ Acc Child pattern ∧
    ∃ S : BoundedRealization stage pattern, S.top = bound}
  have nonempty : badTops.Nonempty := ⟨R.top, a, bad, R, rfl⟩
  obtain ⟨minimum, ⟨parent, badParent, parentRealization, parentTop⟩, minimal⟩ :=
    (wellFounded_lt : WellFounded ((· < ·) : Ordinal.{u} → Ordinal.{u} → Prop)).has_min badTops nonempty
  obtain ⟨child, childOf, badChild⟩ : ∃ child, Child child parent ∧ ¬ Acc Child child := by
    by_contra noChild
    push_neg at noChild
    exact badParent (.intro parent noChild)
  obtain ⟨m, run⟩ := childOf
  obtain ⟨target, j, childRealization, _, smaller, _⟩ := parentRealization.expand_realization run
  have below : RealizationBelow target child (stage.ordinalImage j minimum) :=
    ⟨childRealization, by simpa only [parentTop] using smaller⟩
  obtain ⟨oldChildRealization, oldSmaller⟩ := reflects target j child minimum below
  exact minimal oldChildRealization.top ⟨child, badChild, oldChildRealization, rfl⟩ oldSmaller

end IBLP
