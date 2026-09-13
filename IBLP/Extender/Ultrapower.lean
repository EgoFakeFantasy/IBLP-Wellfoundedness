import IBLP.Extender.GlobalQuantifiers

namespace IBLP.Extender
open FullMarkedBLP FirstOrder Language Derivation
universe u

/-- The global extender quotient of all actual internal representatives
with their rank seeds. Its external well-foundedness is a separate theorem. -/
def Ultrapower {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}
    (D : Derivation stage alpha beta) (ha : Order.IsSuccLimit alpha) (hb : Order.IsSuccLimit beta) :=
  Quotient (GlobalTruth.representativeSetoid D ha hb)

namespace Ultrapower
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}
  (D : Derivation stage alpha beta) (ha : Order.IsSuccLimit alpha) (hb : Order.IsSuccLimit beta)

def mk (r : SeededRepresentative stage alpha beta) : Ultrapower D ha hb := Quotient.mk _ r

theorem mk_eq_iff (r s : SeededRepresentative stage alpha beta) :
    mk D ha hb r = mk D ha hb s ↔ GlobalTruth.Equivalent D ha hb r s := Quotient.eq

theorem mk_surjective : Function.Surjective (mk D ha hb) := Quotient.mk_surjective

def Mem (x y : Ultrapower D ha hb) : Prop :=
  Quotient.liftOn₂ x y (GlobalTruth.Member D ha hb) (by
    intro r s r' s' hr hs
    exact propext (GlobalTruth.member_respects D ha hb hr hs))

theorem mem_mk (r s : SeededRepresentative stage alpha beta) :
    Mem D ha hb (mk D ha hb r) (mk D ha hb s) ↔ GlobalTruth.Member D ha hb r s := Iff.rfl

instance membershipStructure : membershipLanguage.Structure (Ultrapower D ha hb) where
  funMap := fun f => Empty.elim f
  RelMap := fun {n} r xs => by
    obtain ⟨hn⟩ := r
    subst n
    exact Mem D ha hb (xs 0) (xs 1)

def realize {n : Nat} : RankPredicateFormula 0 n → (Fin n → Ultrapower D ha hb) → Prop
  | .falsum, _ => False
  | .equal x y, values => values x = values y
  | .member x y, values => Mem D ha hb (values x) (values y)
  | .predicate a _, _ => Fin.elim0 a
  | .imp p q, values => realize p values → realize q values
  | .all p, values => ∀ x, realize p (Fin.snoc values x)

theorem los {n : Nat} (phi : RankPredicateFormula 0 n)
    (rs : Fin n → SeededRepresentative stage alpha beta) :
    realize D ha hb phi (mk D ha hb ∘ rs) ↔ GlobalTruth.Holds D ha hb phi rs := by
  induction phi with
  | falsum => exact iff_of_false id (GlobalTruth.not_falsum D ha hb rs)
  | equal x y =>
    change mk D ha hb (rs x) = mk D ha hb (rs y) ↔ _
    rw [mk_eq_iff]
    have h := GlobalTruth.reindex_iff D ha hb (.equal 0 1) rs ![x, y]
    have args : rs ∘ ![x, y] = ![rs x, rs y] := by funext i; fin_cases i <;> rfl
    rw [args] at h
    exact h
  | member x y =>
    change Mem D ha hb (mk D ha hb (rs x)) (mk D ha hb (rs y)) ↔ _
    rw [mem_mk]
    have h := GlobalTruth.reindex_iff D ha hb (.member 0 1) rs ![x, y]
    have args : rs ∘ ![x, y] = ![rs x, rs y] := by funext i; fin_cases i <;> rfl
    rw [args] at h
    exact h
  | predicate a _ => exact Fin.elim0 a
  | imp p q ihp ihq =>
    change (_ → _) ↔ _
    rw [ihp, ihq, GlobalTruth.imp_iff]
  | @all n p ih =>
    change (∀ x, realize D ha hb p (Fin.snoc (mk D ha hb ∘ rs) x)) ↔ _
    rw [GlobalTruth.all_iff]
    have args (r : SeededRepresentative stage alpha beta) :
        mk D ha hb ∘ Fin.snoc rs r = Fin.snoc (mk D ha hb ∘ rs) (mk D ha hb r) := by
      funext i
      cases i using Fin.lastCases with
      | last => simp
      | cast i => simp
    constructor
    · intro h r
      apply (ih (Fin.snoc rs r)).mp
      rw [args]
      exact h (mk D ha hb r)
    · intro h x
      obtain ⟨r, rfl⟩ := mk_surjective D ha hb x
      rw [← args]
      exact (ih (Fin.snoc rs r)).mpr (h r)

end Ultrapower
end IBLP.Extender
