import IBLP.Extender.UltrapowerAt

namespace IBLP.Extender.UltrapowerAt
open FullMarkedBLP FirstOrder Language Derivation
universe u
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}
  (D : Derivation stage alpha beta) (seed : Seed stage beta)

theorem memAt_realize {a : Type} {n : Nat} (x y : a ⊕ Fin n)
    (free : a → UltrapowerAt D seed) (bound : Fin n → UltrapowerAt D seed) :
    (rankMemAt x y).Realize free bound ↔ Mem D seed (Sum.elim free bound x) (Sum.elim free bound y) := by
  simp [rankMemAt, BoundedFormula.Realize, Relations.boundedFormula₂,
    Relations.boundedFormula, Structure.RelMap]

theorem term_realize {a : Type} (term : membershipLanguage.Term a) (values : a → UltrapowerAt D seed) :
    term.realize values = values (rankPureTermVariable term) := by
  cases term with
  | var => rfl
  | func f _ => exact Empty.elim f

/-- Native first-order syntax is interpreted in the actual quotient
membership structure, not in a surrogate truth predicate. -/
theorem translate_realize {a : Type} {k n : Nat}
    (phi : membershipLanguage.BoundedFormula a k) (indices : a ⊕ Fin k → Fin n)
    (values : Fin n → UltrapowerAt D seed) (free : a → UltrapowerAt D seed)
    (bound : Fin k → UltrapowerAt D seed)
    (compatible : ∀ i, values (indices i) = Sum.elim free bound i) :
    realize D seed (rankPureTranslate phi indices) values ↔ phi.Realize free bound := by
  induction phi generalizing n with
  | falsum => rfl
  | equal x y =>
    simp only [rankPureTranslate, realize, BoundedFormula.Realize, term_realize, compatible]
  | @rel k arity relation terms =>
    obtain ⟨same⟩ := relation
    subst arity
    simp only [rankPureTranslate, realize, BoundedFormula.Realize, Structure.RelMap, term_realize, compatible]
  | imp p q ihp ihq => exact imp_congr (ihp indices values bound compatible) (ihq indices values bound compatible)
  | all p ih =>
    apply forall_congr'
    intro x
    apply ih (rankPureLift indices) (Fin.snoc values x) (Fin.snoc bound x)
    intro i
    cases i with
    | inl a => simpa [rankPureLift, Fin.snoc] using compatible (.inl a)
    | inr i =>
      cases i using Fin.lastCases with
      | last => simp [rankPureLift, Fin.snoc]
      | cast i => simpa [rankPureLift, Fin.snoc] using compatible (.inr i)

theorem realize_atom {n k : Nat} (phi : membershipLanguage.Formula (Fin k))
    (indices : Fin k → Fin n) (values : Fin n → UltrapowerAt D seed) :
    realize D seed (rankPredicateAtom phi indices) values ↔ phi.Realize (values ∘ indices) := by
  apply translate_realize D seed phi _ values (values ∘ indices) Fin.elim0
  intro i
  cases i with
  | inl => rfl
  | inr i => exact Fin.elim0 i

theorem los_formula {n : Nat} (phi : membershipLanguage.Formula (Fin n))
    (fs : Fin n → Representative stage alpha) :
    phi.Realize (mk D seed ∘ fs) ↔ D.Holds seed (rankPredicateAtom phi id) fs := by
  have h := los D seed (rankPredicateAtom phi id) fs
  rwa [realize_atom, Function.comp_id] at h

/-- The native quotient semantics agrees with membership in the actual
derived measure set in M. -/
theorem los_measure {n : Nat} (phi : membershipLanguage.Formula (Fin n))
    (fs : Fin n → Representative stage alpha) :
    phi.Realize (mk D seed ∘ fs) ↔
      (formulaTest (rankPredicateAtom phi id) fs).val ∈ (D.measure seed).val := by
  rw [los_formula, D.mem_measure_test_iff]
  rfl

end IBLP.Extender.UltrapowerAt
