import IBLP.Model.Formula
import IBLP.Rank.Restriction

namespace IBLP
open FullMarkedBLP FirstOrder Language
universe u

/-- 一个实际集合的全部成员；该集合本身不必传递。 -/
def SetDomain (domain : ZFSet.{u}) := {x : ZFSet.{u} // x ∈ domain}

namespace SetDomain

instance membershipStructure (domain : ZFSet.{u}) : membershipLanguage.Structure (SetDomain domain) where
  funMap := fun f => Empty.elim f
  RelMap := fun {n} r xs => by
    obtain ⟨hn⟩ := r
    subst n
    exact (xs 0).val ∈ (xs 1).val

def realize (domain : ZFSet.{u}) {n : Nat} :
    RankPredicateFormula 0 n → (Fin n → SetDomain domain) → Prop
  | .falsum, _ => False
  | .equal x y, values => values x = values y
  | .member x y, values => (values x).val ∈ (values y).val
  | .predicate a _, _ => Fin.elim0 a
  | .imp p q, values => realize domain p values → realize domain q values
  | .all p, values => ∀ x, realize domain p (Fin.snoc values x)

theorem memAt_realize (domain : ZFSet.{u}) {alpha : Type} {n : Nat}
    (x y : alpha ⊕ Fin n) (free : alpha → SetDomain domain) (bound : Fin n → SetDomain domain) :
    (rankMemAt x y).Realize free bound ↔
      (Sum.elim free bound x).val ∈ (Sum.elim free bound y).val := by
  simp [rankMemAt, BoundedFormula.Realize, Relations.boundedFormula₂,
    Relations.boundedFormula, Structure.RelMap]

theorem pureTranslate_realize (domain : ZFSet.{u}) {alpha : Type} {n k : Nat}
    (phi : RankPredicateFormula 0 n) (indices : Fin n → alpha ⊕ Fin k)
    (values : Fin n → SetDomain domain) (free : alpha → SetDomain domain)
    (bound : Fin k → SetDomain domain)
    (compatible : ∀ i, values i = Sum.elim free bound (indices i)) :
    realize domain phi values ↔ (rankPredicatePureTranslate phi indices).Realize free bound := by
  induction phi generalizing k with
  | falsum => rfl
  | equal x y =>
    change values x = values y ↔ Sum.elim free bound (indices x) = Sum.elim free bound (indices y)
    rw [compatible, compatible]
  | member x y =>
    rw [rankPredicatePureTranslate, memAt_realize]
    change (values x).val ∈ (values y).val ↔ _
    rw [compatible, compatible]
  | predicate a _ => exact Fin.elim0 a
  | imp p q ihp ihq => exact imp_congr (ihp indices values bound compatible) (ihq indices values bound compatible)
  | all p ih =>
    change (∀ x, realize domain p (Fin.snoc values x)) ↔
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

theorem realize_toFormula (domain : ZFSet.{u}) {n : Nat}
    (phi : RankPredicateFormula 0 n) (values : Fin n → SetDomain domain) :
    realize domain phi values ↔ (rankPredicateToFormula phi).Realize values :=
  pureTranslate_realize domain phi Sum.inl values values Fin.elim0 (fun _ => rfl)

theorem term_realize (domain : ZFSet.{u}) {alpha : Type}
    (term : membershipLanguage.Term alpha) (values : alpha → SetDomain domain) :
    term.realize values = values (rankPureTermVariable term) := by
  cases term with
  | var => rfl
  | func f _ => exact Empty.elim f

theorem translate_realize (domain : ZFSet.{u}) {alpha : Type} {k n : Nat}
    (phi : membershipLanguage.BoundedFormula alpha k) (indices : alpha ⊕ Fin k → Fin n)
    (values : Fin n → SetDomain domain) (free : alpha → SetDomain domain)
    (bound : Fin k → SetDomain domain)
    (compatible : ∀ i, values (indices i) = Sum.elim free bound i) :
    realize domain (rankPureTranslate phi indices) values ↔ phi.Realize free bound := by
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

theorem realize_atom (domain : ZFSet.{u}) {n : Nat}
    (phi : membershipLanguage.Formula (Fin n)) (values : Fin n → SetDomain domain) :
    realize domain (rankPredicateAtom phi id) values ↔ phi.Realize values := by
  apply translate_realize domain phi _ values values Fin.elim0
  intro i
  cases i with
  | inl => rfl
  | inr i => exact Fin.elim0 i

end SetDomain

namespace TransitiveClass

def setInclude (M : TransitiveClass.{u}) (domain : M.Element) : SetDomain domain.val → M.Element :=
  fun x => M.member domain x.val x.property

/-- 量词限制到内部集合，恰好得到它的全部实际成员结构；不用宇宙真谓词。 -/
theorem restrictFormula_realize (M : TransitiveClass.{u}) (set : M.Element)
    {n k : Nat} (phi : RankPredicateFormula 0 n) (indices : Fin n → Fin k) (domain : Fin k)
    (values : Fin n → SetDomain set.val) (outer : Fin k → M.Element)
    (hVars : ∀ i, (outer (indices i)).val = (values i).val)
    (hDomain : outer domain = set) :
    M.realize (restrictFormula phi indices domain) outer ↔ SetDomain.realize set.val phi values := by
  induction phi generalizing k with
  | falsum => rfl
  | equal x y =>
    change (outer (indices x) = outer (indices y)) ↔ values x = values y
    constructor
    · intro h
      apply Subtype.ext
      exact (hVars x).symm.trans ((congrArg Subtype.val h).trans (hVars y))
    · intro h
      apply Subtype.ext
      exact (hVars x).trans ((congrArg Subtype.val h).trans (hVars y).symm)
  | member x y =>
    change (outer (indices x)).val ∈ (outer (indices y)).val ↔ _
    rw [hVars, hVars]
    rfl
  | predicate a _ => exact Fin.elim0 a
  | imp p q ihp ihq =>
    exact imp_congr (ihp indices domain values outer hVars hDomain)
      (ihq indices domain values outer hVars hDomain)
  | @all n p ih =>
    simp only [restrictFormula, realize, SetDomain.realize, Fin.snoc_last, Fin.snoc_castSucc]
    change (∀ x : M.Element, x.val ∈ (outer domain).val →
      M.realize (restrictFormula p (Fin.lastCases (Fin.last k) (fun i => (indices i).castSucc))
        domain.castSucc) (Fin.snoc outer x)) ↔
      ∀ y : SetDomain set.val, SetDomain.realize set.val p (Fin.snoc values y)
    have body (x : M.Element) (y : SetDomain set.val) (hxy : x.val = y.val) :
        M.realize (restrictFormula p (Fin.lastCases (Fin.last k) (fun i => (indices i).castSucc))
          domain.castSucc) (Fin.snoc outer x) ↔ SetDomain.realize set.val p (Fin.snoc values y) := by
      apply ih _ _ (Fin.snoc values y) (Fin.snoc outer x)
      · intro i
        cases i using Fin.lastCases with
        | last => simpa only [Fin.lastCases_last, Fin.snoc_last] using hxy
        | cast i => simpa only [Fin.lastCases_castSucc, Fin.snoc_castSucc] using hVars i
      · simpa only [Fin.snoc_castSucc] using hDomain
    constructor
    · intro h y
      apply (body (M.setInclude set y) y rfl).mp
      apply h
      simpa only [hDomain] using y.property
    · intro h x hx
      have hm : x.val ∈ set.val := hDomain ▸ hx
      exact (body x ⟨x.val, hm⟩ rfl).mpr (h ⟨x.val, hm⟩)

/-- 每个有限原生公式均产生一个有限的相对化公式。 -/
def setFormula {n : Nat} (phi : membershipLanguage.Formula (Fin n)) : RankPredicateFormula 0 (n + 1) :=
  restrictFormula (rankPredicateAtom phi id) Fin.castSucc (Fin.last n)

theorem setFormula_realize (M : TransitiveClass.{u}) (domain : M.Element) {n : Nat}
    (phi : membershipLanguage.Formula (Fin n)) (values : Fin n → SetDomain domain.val) :
    M.realize (setFormula phi) (Fin.snoc (M.setInclude domain ∘ values) domain) ↔ phi.Realize values := by
  rw [← SetDomain.realize_atom]
  apply M.restrictFormula_realize domain
  · intro i
    simp only [Fin.snoc_castSucc, Function.comp_apply, setInclude, member]
  · simp only [Fin.snoc_last]

end TransitiveClass
end IBLP
