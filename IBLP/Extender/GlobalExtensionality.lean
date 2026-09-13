import IBLP.Extender.GlobalEmbedding

namespace IBLP.Extender
open FullMarkedBLP Derivation
universe u

def extensionalityMatrix : RankPredicateFormula 0 2 :=
  (RankPredicateFormula.all ((RankPredicateFormula.member 2 0).iff (.member 2 1))).imp (.equal 0 1)

theorem model_extensionality (M : TransitiveClass.{u}) (values : Fin 2 → M.Element) :
    M.realize extensionalityMatrix values := by
  have sem : M.realize extensionalityMatrix values ↔
      ((∀ z : M.Element, z.val ∈ (values 0).val ↔ z.val ∈ (values 1).val) → values 0 = values 1) := by
    simp [extensionalityMatrix, RankPredicateFormula.iff, RankPredicateFormula.and,
      RankPredicateFormula.not, TransitiveClass.realize, Fin.snoc, iff_def]
  apply sem.mpr
  intro h
  apply Subtype.ext
  apply ZFSet.ext
  intro z
  exact ⟨fun hz => (h (M.member (values 0) z hz)).mp hz,
    fun hz => (h (M.member (values 1) z hz)).mpr hz⟩

namespace Ultrapower
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}
  (D : Derivation stage alpha beta) (ha : Order.IsSuccLimit alpha) (hb : Order.IsSuccLimit beta)

theorem realize_of_valid {n : Nat} (phi : RankPredicateFormula 0 n)
    (h : ∀ values : Fin n → stage.model.Element, stage.model.realize phi values)
    (values : Fin n → Ultrapower D ha hb) : realize D ha hb phi values := by
  classical
  let rs := fun i => Classical.choose (mk_surjective D ha hb (values i))
  have same : mk D ha hb ∘ rs = values :=
    funext (fun i => Classical.choose_spec (mk_surjective D ha hb (values i)))
  rw [← same]
  exact (los D ha hb phi rs).mpr (GlobalTruth.of_valid D ha hb phi rs h)

/-- Extensionality is proved for the actual global membership quotient.
It does not assert external well-foundedness or set-like predecessors. -/
theorem extensional (x y : Ultrapower D ha hb)
    (h : ∀ z, Mem D ha hb z x ↔ Mem D ha hb z y) : x = y := by
  have valid := realize_of_valid D ha hb extensionalityMatrix (model_extensionality stage.model) ![x, y]
  have sem : realize D ha hb extensionalityMatrix ![x, y] ↔
      ((∀ z, Mem D ha hb z x ↔ Mem D ha hb z y) → x = y) := by
    simp [extensionalityMatrix, RankPredicateFormula.iff, RankPredicateFormula.and,
      RankPredicateFormula.not, realize, Fin.snoc, iff_def]
  exact sem.mp valid h

end Ultrapower
end IBLP.Extender
