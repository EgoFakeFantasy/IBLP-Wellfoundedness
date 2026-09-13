import IBLP.Model.TransitiveClass
import FullMarkedBLP.RankTruthFormulaAtoms

namespace IBLP
open FullMarkedBLP FirstOrder Language

universe u

namespace TransitiveClass

/-- 复用有限纯成员语法，量词范围严格是当前模型的元素。 -/
def realize (M : TransitiveClass.{u}) {n : Nat} :
    RankPredicateFormula 0 n → (Fin n → M.Element) → Prop
  | .falsum, _ => False
  | .equal x y, values => values x = values y
  | .member x y, values => (values x).val ∈ (values y).val
  | .predicate a _, _ => Fin.elim0 a
  | .imp p q, values => M.realize p values → M.realize q values
  | .all p, values => ∀ x : M.Element, M.realize p (Fin.snoc values x)

theorem realize_not (M : TransitiveClass.{u}) {n : Nat} (p : RankPredicateFormula 0 n)
    (values : Fin n → M.Element) : M.realize p.not values ↔ ¬ M.realize p values := Iff.rfl

theorem realize_and (M : TransitiveClass.{u}) {n : Nat} (p q : RankPredicateFormula 0 n)
    (values : Fin n → M.Element) : M.realize (p.and q) values ↔ M.realize p values ∧ M.realize q values := by
  classical
  simp [RankPredicateFormula.and, RankPredicateFormula.not, realize]

theorem realize_ex (M : TransitiveClass.{u}) {n : Nat} (p : RankPredicateFormula 0 (n + 1))
    (values : Fin n → M.Element) : M.realize p.ex values ↔ ∃ x, M.realize p (Fin.snoc values x) := by
  classical
  simp [RankPredicateFormula.ex, RankPredicateFormula.not, realize]

theorem memAt_realize (M : TransitiveClass.{u}) {alpha : Type} {n : Nat}
    (x y : alpha ⊕ Fin n) (free : alpha → M.Element) (bound : Fin n → M.Element) :
    (rankMemAt x y).Realize free bound ↔
      (Sum.elim free bound x).val ∈ (Sum.elim free bound y).val := by
  simp [rankMemAt, BoundedFormula.Realize, Relations.boundedFormula₂,
    Relations.boundedFormula, Structure.RelMap]

theorem pureTranslate_realize (M : TransitiveClass.{u}) {alpha : Type} {n k : Nat}
    (phi : RankPredicateFormula 0 n) (indices : Fin n → alpha ⊕ Fin k)
    (values : Fin n → M.Element) (free : alpha → M.Element) (bound : Fin k → M.Element)
    (compatible : ∀ i, values i = Sum.elim free bound (indices i)) :
    M.realize phi values ↔ (rankPredicatePureTranslate phi indices).Realize free bound := by
  induction phi generalizing k with
  | falsum => rfl
  | equal x y =>
    change values x = values y ↔ Sum.elim free bound (indices x) = Sum.elim free bound (indices y)
    rw [compatible, compatible]
  | member x y =>
    rw [rankPredicatePureTranslate, M.memAt_realize]
    change (values x).val ∈ (values y).val ↔ _
    rw [compatible, compatible]
  | predicate a _ => exact Fin.elim0 a
  | imp p q ihp ihq => exact imp_congr (ihp indices values bound compatible) (ihq indices values bound compatible)
  | all p ih =>
    change (∀ x, M.realize p (Fin.snoc values x)) ↔
      ∀ x, (rankPredicatePureTranslate p (rankPredicateOldLift indices)).Realize free (Fin.snoc bound x)
    apply forall_congr'
    intro x
    apply ih (rankPredicateOldLift indices) (Fin.snoc values x) (Fin.snoc bound x)
    intro i
    cases i using Fin.lastCases with
    | last => simp [rankPredicateOldLift]
    | cast i =>
      cases hi : indices i with
      | inl a => simpa [rankPredicateOldLift, hi] using compatible i
      | inr b => simpa [rankPredicateOldLift, hi] using compatible i

theorem realize_toFormula (M : TransitiveClass.{u}) {n : Nat}
    (phi : RankPredicateFormula 0 n) (values : Fin n → M.Element) :
    M.realize phi values ↔ (rankPredicateToFormula phi).Realize values :=
  M.pureTranslate_realize phi Sum.inl values values Fin.elim0 (fun _ => rfl)

theorem ElementaryMap.realize_iff {M N : TransitiveClass.{u}} (j : M.ElementaryMap N)
    {n : Nat} (phi : RankPredicateFormula 0 n) (values : Fin n → M.Element) :
    N.realize phi (j ∘ values) ↔ M.realize phi values := by
  rw [N.realize_toFormula, M.realize_toFormula]
  exact j.map_formula _ values

theorem term_realize (M : TransitiveClass.{u}) {alpha : Type}
    (term : membershipLanguage.Term alpha) (values : alpha → M.Element) :
    term.realize values = values (rankPureTermVariable term) := by
  cases term with
  | var => rfl
  | func f _ => exact Empty.elim f

theorem translate_realize (M : TransitiveClass.{u}) {alpha : Type} {k n : Nat}
    (phi : membershipLanguage.BoundedFormula alpha k) (indices : alpha ⊕ Fin k → Fin n)
    (values : Fin n → M.Element) (free : alpha → M.Element) (bound : Fin k → M.Element)
    (compatible : ∀ i, values (indices i) = Sum.elim free bound i) :
    M.realize (rankPureTranslate phi indices) values ↔ phi.Realize free bound := by
  induction phi generalizing n with
  | falsum => rfl
  | equal x y =>
    simp only [rankPureTranslate, realize, BoundedFormula.Realize, M.term_realize, compatible]
  | @rel k arity relation terms =>
    obtain ⟨same⟩ := relation
    subst arity
    simp only [rankPureTranslate, realize, BoundedFormula.Realize, Structure.RelMap, M.term_realize, compatible]
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

theorem realize_atom (M : TransitiveClass.{u}) {n k : Nat}
    (phi : membershipLanguage.Formula (Fin k)) (indices : Fin k → Fin n) (values : Fin n → M.Element) :
    M.realize (rankPredicateAtom phi indices) values ↔ phi.Realize (values ∘ indices) := by
  apply M.translate_realize phi _ values (values ∘ indices) Fin.elim0
  intro i
  cases i with
  | inl => rfl
  | inr i => exact Fin.elim0 i

end TransitiveClass
end IBLP
