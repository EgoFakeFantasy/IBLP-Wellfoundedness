import IBLP.Extender.Ultrapower

namespace IBLP.Extender.Ultrapower
open FullMarkedBLP FirstOrder Language Derivation
universe u
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}
  (D : Derivation stage alpha beta) (ha : Order.IsSuccLimit alpha) (hb : Order.IsSuccLimit beta)

theorem memAt_realize {a : Type} {n : Nat} (x y : a ⊕ Fin n)
    (free : a → Ultrapower D ha hb) (bound : Fin n → Ultrapower D ha hb) :
    (rankMemAt x y).Realize free bound ↔ Mem D ha hb (Sum.elim free bound x) (Sum.elim free bound y) := by
  simp [rankMemAt, BoundedFormula.Realize, Relations.boundedFormula₂,
    Relations.boundedFormula, Structure.RelMap]

theorem term_realize {a : Type} (term : membershipLanguage.Term a) (values : a → Ultrapower D ha hb) :
    term.realize values = values (rankPureTermVariable term) := by
  cases term with
  | var => rfl
  | func f _ => exact Empty.elim f

theorem translate_realize {a : Type} {k n : Nat}
    (phi : membershipLanguage.BoundedFormula a k) (indices : a ⊕ Fin k → Fin n)
    (values : Fin n → Ultrapower D ha hb) (free : a → Ultrapower D ha hb)
    (bound : Fin k → Ultrapower D ha hb)
    (compatible : ∀ i, values (indices i) = Sum.elim free bound i) :
    realize D ha hb (rankPureTranslate phi indices) values ↔ phi.Realize free bound := by
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
    (indices : Fin k → Fin n) (values : Fin n → Ultrapower D ha hb) :
    realize D ha hb (rankPredicateAtom phi indices) values ↔ phi.Realize (values ∘ indices) := by
  apply translate_realize D ha hb phi _ values (values ∘ indices) Fin.elim0
  intro i
  cases i with
  | inl => rfl
  | inr i => exact Fin.elim0 i

/-- Full native first-order Los theorem for the global extender quotient. -/
theorem los_formula {n : Nat} (phi : membershipLanguage.Formula (Fin n))
    (rs : Fin n → SeededRepresentative stage alpha beta) :
    phi.Realize (mk D ha hb ∘ rs) ↔ GlobalTruth.Holds D ha hb (rankPredicateAtom phi id) rs := by
  have h := los D ha hb (rankPredicateAtom phi id) rs
  rwa [realize_atom, Function.comp_id] at h

/-- The global quotient truth can be computed at any common refinement,
using membership in its actual derived measure set in M. -/
theorem los_measure {n : Nat} (phi : membershipLanguage.Formula (Fin n))
    (rs : Fin n → SeededRepresentative stage alpha beta)
    (R : CommonRefinement D (fun i => (rs i).seed)) :
    phi.Realize (mk D ha hb ∘ rs) ↔
      (formulaTest (rankPredicateAtom phi id) (fun i => (rs i).representative.pullback (R.maps i))).val ∈
        (D.measure R.seed).val := by
  rw [los_formula, GlobalTruth.at_refinement D ha hb _ rs R, D.mem_measure_test_iff]
  rfl

end IBLP.Extender.Ultrapower
