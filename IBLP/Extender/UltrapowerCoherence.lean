import IBLP.Extender.UltrapowerTransition

namespace IBLP.Extender
open FullMarkedBLP FirstOrder Language Derivation
universe u
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}

theorem Representative.indexValue_comp (limit : Order.IsSuccLimit alpha)
    (p q : IndexMap stage alpha) (x : Seed stage alpha) :
    Representative.indexValue (p.comp limit q) x =
      Representative.indexValue q (Representative.indexValue p x) := by
  apply Subtype.ext
  exact ((p.comp limit q).function.2 x.val ((stage.mem_hierarchy alpha x.val).mpr x.property)).unique
    (Representative.indexValue_edge (p.comp limit q) x)
    ((p.comp_edge_iff limit q _ _).mpr ⟨(Representative.indexValue p x).val,
      Representative.indexValue_edge p x, Representative.indexValue_edge q _⟩)

namespace UltrapowerAt
variable (D : Derivation stage alpha beta)

/-- Equality of seeds transports the actual quotient structure. -/
def seedCongr {a b : Seed stage beta} (h : a = b) :
    ElementaryEmbedding membershipLanguage (UltrapowerAt D a) (UltrapowerAt D b) := by
  subst b
  exact ElementaryEmbedding.refl _ _

theorem seedCongr_mk {a b : Seed stage beta} (h : a = b) (f : Representative stage alpha) :
    seedCongr D h (mk D a f) = mk D b f := by
  subst b
  rfl

theorem seedCongr_constant {a b : Seed stage beta} (h : a = b) (x : stage.model.Element) :
    seedCongr D h (constantEmbedding D a x) = constantEmbedding D b x :=
  seedCongr_mk D h (Representative.constant x)

/-- Pullbacks compose contravariantly; the seed equality is supplied by
the already proved action of the original bounded elementary graph. -/
theorem transition_comp (seed : Seed stage beta) (limit : Order.IsSuccLimit alpha)
    (p q : IndexMap stage alpha) (x : UltrapowerAt D (D.project q (D.project p seed))) :
    transition D seed (p.comp limit q) (seedCongr D (D.project_comp limit p q seed).symm x) =
      transition D seed p (transition D (D.project p seed) q x) := by
  obtain ⟨f, rfl⟩ := mk_surjective D (D.project q (D.project p seed)) x
  rw [seedCongr_mk, transition_mk, transition_mk, transition_mk]
  apply (mk_eq_iff D seed _ _).mpr
  apply D.holds_of_pointwise
  intro z
  change (f.pullback (p.comp limit q)).value z = ((f.pullback q).pullback p).value z
  simp only [Representative.pullback_value, Representative.indexValue_comp]

/-- Any finite list of components embeds into one common component, and
each embedding preserves the same constant copy of the original model.
This is a finite common-component interface, not a direct-limit theorem. -/
theorem finite_common (ha : Order.IsSuccLimit alpha) (hb : Order.IsSuccLimit beta)
    {n : Nat} (seeds : Fin n → Seed stage beta) :
    ∃ common : Seed stage beta, ∃ embeddings : ∀ i,
      ElementaryEmbedding membershipLanguage (UltrapowerAt D (seeds i)) (UltrapowerAt D common),
      ∀ i x, embeddings i (constantEmbedding D (seeds i) x) = constantEmbedding D common x := by
  obtain ⟨common, projections, project_eq⟩ := D.finite_directed ha hb seeds
  refine ⟨common, (fun i => (transitionEmbedding D common (projections i)).comp
    (seedCongr D (project_eq i).symm)), ?_⟩
  intro i x
  rw [ElementaryEmbedding.comp_apply, seedCongr_constant]
  exact transition_constant D common (projections i) x

end UltrapowerAt
end IBLP.Extender
