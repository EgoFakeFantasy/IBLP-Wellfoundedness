import IBLP.Extender.RepresentativeEquality

namespace IBLP.Extender
open FullMarkedBLP FirstOrder Language
universe u

/-- One component of the derived system: the quotient of actual internal
function graphs at a fixed rank seed. No well-foundedness is asserted here. -/
def UltrapowerAt {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}
    (D : Derivation stage alpha beta) (seed : Derivation.Seed stage beta) :=
  Quotient (D.representativeSetoid seed)

namespace UltrapowerAt
open Derivation
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}
  (D : Derivation stage alpha beta) (seed : Seed stage beta)

def mk (f : Representative stage alpha) : UltrapowerAt D seed := Quotient.mk _ f

theorem mk_eq_iff (f g : Representative stage alpha) :
    mk D seed f = mk D seed g ↔ D.RepEquivalent seed f g := Quotient.eq

theorem mk_surjective : Function.Surjective (mk D seed) := Quotient.mk_surjective

def Mem (x y : UltrapowerAt D seed) : Prop :=
  Quotient.liftOn₂ x y (fun f g => D.Holds seed (.member 0 1) ![f, g]) (by
    intro f g f' g' hf hg
    apply propext
    apply D.holds_respects seed
    intro i
    fin_cases i
    · exact hf
    · exact hg)

theorem mem_mk (f g : Representative stage alpha) :
    Mem D seed (mk D seed f) (mk D seed g) ↔ D.Holds seed (.member 0 1) ![f, g] := Iff.rfl

instance membershipStructure : membershipLanguage.Structure (UltrapowerAt D seed) where
  funMap := fun f => Empty.elim f
  RelMap := fun {n} r xs => by
    obtain ⟨hn⟩ := r
    subst n
    exact Mem D seed (xs 0) (xs 1)

def realize {n : Nat} : RankPredicateFormula 0 n → (Fin n → UltrapowerAt D seed) → Prop
  | .falsum, _ => False
  | .equal x y, v => v x = v y
  | .member x y, v => Mem D seed (v x) (v y)
  | .predicate a _, _ => Fin.elim0 a
  | .imp p q, v => realize p v → realize q v
  | .all p, v => ∀ x, realize p (Fin.snoc v x)

/-- Full finite-formula Los theorem for a fixed seed. The quantifier step
uses the internally constructed choice graph, not an external function. -/
theorem los {n : Nat} (phi : RankPredicateFormula 0 n) (fs : Fin n → Representative stage alpha) :
    realize D seed phi (mk D seed ∘ fs) ↔ D.Holds seed phi fs := by
  induction phi with
  | falsum => exact iff_of_false id (D.not_holds_falsum seed fs)
  | equal x y =>
    change mk D seed (fs x) = mk D seed (fs y) ↔ _
    rw [mk_eq_iff]
    exact D.holds_congr seed (.equal 0 1) (.equal x y) ![fs x, fs y] fs (fun _ => Iff.rfl)
  | member x y =>
    change Mem D seed (mk D seed (fs x)) (mk D seed (fs y)) ↔ _
    rw [mem_mk]
    exact D.holds_congr seed (.member 0 1) (.member x y) ![fs x, fs y] fs (fun _ => Iff.rfl)
  | predicate a _ => exact Fin.elim0 a
  | imp p q ihp ihq =>
    change (_ → _) ↔ _
    rw [ihp, ihq, D.holds_imp_iff]
  | @all n p ih =>
    change (∀ x, realize D seed p (Fin.snoc (mk D seed ∘ fs) x)) ↔ _
    rw [D.holds_all_iff]
    have args (f : Representative stage alpha) :
        mk D seed ∘ Fin.snoc fs f = Fin.snoc (mk D seed ∘ fs) (mk D seed f) := by
      funext i
      cases i using Fin.lastCases with
      | last => simp
      | cast i => simp
    constructor
    · intro h f
      apply (ih (Fin.snoc fs f)).mp
      rw [args]
      exact h (mk D seed f)
    · intro h x
      obtain ⟨f, rfl⟩ := mk_surjective D seed x
      rw [← args]
      exact (ih (Fin.snoc fs f)).mpr (h f)

end UltrapowerAt
end IBLP.Extender
