import IBLP.Model.Graph
import IBLP.Model.Powerset
import FullMarkedBLP.RankOntoFormula
import FullMarkedBLP.RankCofinalFormula
import FullMarkedBLP.RankOmegaPreservation

namespace IBLP
open FullMarkedBLP FirstOrder Language
universe u

/-- Onto is an assertion about the actual members of a set graph. -/
def setGraphOnto (f x y : ZFSet.{u}) : Prop :=
  ∀ b ∈ y, ∃ a ∈ x, ZFSet.pair a b ∈ f

def setGraphCofinal (f x y : ZFSet.{u}) : Prop :=
  ∀ b ∈ y, ∃ a ∈ x, ∃ c ∈ y, ZFSet.pair a c ∈ f ∧ b ∈ c

def setNonzeroLimit (x : ZFSet.{u}) : Prop :=
  (∃ z, z ∈ x) ∧ ∀ z ∈ x, ∃ w ∈ x, z ∈ w

def setFirstLimit (x : ZFSet.{u}) : Prop :=
  setNonzeroLimit x ∧ ∀ z ∈ x, ¬setNonzeroLimit z

namespace TransitiveClass

theorem ontoFormula_absolute (M : TransitiveClass.{u}) (f x y : M.Element) :
    rankOntoFormula.Realize ![f, x, y] ↔ setGraphOnto f.val x.val y.val := by
  have sem : rankOntoFormula.Realize ![f, x, y] ↔
      ∀ b : M.Element, b.val ∈ y.val → ∃ a : M.Element,
        a.val ∈ x.val ∧ M.GraphApplies f a b := by
    simp [rankOntoFormula, Formula.Realize, BoundedFormula.Realize,
      M.memAt_realize, M.graphAppliesAt_realize, Fin.snoc]
  rw [sem]
  constructor
  · intro h b hb
    obtain ⟨a, ha, hf⟩ := h (M.member y b hb) hb
    exact ⟨a.val, ha, (M.graphApplies_absolute _ _ _).mp hf⟩
  · intro h b hb
    obtain ⟨a, ha, hf⟩ := h b.val hb
    exact ⟨M.member x a ha, ha, (M.graphApplies_absolute _ _ _).mpr hf⟩

theorem cofinalFormula_absolute (M : TransitiveClass.{u}) (f x y : M.Element) :
    rankCofinalFormula.Realize ![f, x, y] ↔ setGraphCofinal f.val x.val y.val := by
  have sem : rankCofinalFormula.Realize ![f, x, y] ↔
      ∀ b : M.Element, b.val ∈ y.val → ∃ a : M.Element, a.val ∈ x.val ∧
        ∃ c : M.Element, c.val ∈ y.val ∧ M.GraphApplies f a c ∧ b.val ∈ c.val := by
    simp [rankCofinalFormula, Formula.Realize, BoundedFormula.Realize,
      M.memAt_realize, M.graphAppliesAt_realize, Fin.snoc]
  rw [sem]
  constructor
  · intro h b hb
    obtain ⟨a, ha, c, hc, hf, hbc⟩ := h (M.member y b hb) hb
    exact ⟨a.val, ha, c.val, hc, (M.graphApplies_absolute _ _ _).mp hf, hbc⟩
  · intro h b hb
    obtain ⟨a, ha, c, hc, hf, hbc⟩ := h b.val hb
    exact ⟨M.member x a ha, ha, M.member y c hc, hc,
      (M.graphApplies_absolute _ _ _).mpr hf, hbc⟩

theorem nonzeroLimitFormula_absolute (M : TransitiveClass.{u}) (x : M.Element) :
    rankNonzeroLimitFormula.Realize ![x] ↔ setNonzeroLimit x.val := by
  have sem : rankNonzeroLimitFormula.Realize ![x] ↔
      (∃ z : M.Element, z.val ∈ x.val) ∧ ∀ z : M.Element, z.val ∈ x.val →
        ∃ w : M.Element, w.val ∈ x.val ∧ z.val ∈ w.val := by
    simp [rankNonzeroLimitFormula, Formula.Realize, BoundedFormula.Realize,
      M.memAt_realize, Fin.snoc]
  rw [sem]
  constructor
  · rintro ⟨⟨z, hz⟩, h⟩
    refine ⟨⟨z.val, hz⟩, ?_⟩
    intro a ha
    obtain ⟨w, hw, haw⟩ := h (M.member x a ha) ha
    exact ⟨w.val, hw, haw⟩
  · rintro ⟨⟨z, hz⟩, h⟩
    refine ⟨⟨M.member x z hz, hz⟩, ?_⟩
    intro a ha
    obtain ⟨w, hw, haw⟩ := h a.val ha
    exact ⟨M.member x w hw, hw, haw⟩

theorem nonzeroLimitAt_absolute (M : TransitiveClass.{u}) {a : Type} {n : Nat}
    (x : a ⊕ Fin n) (free : a → M.Element) (bound : Fin n → M.Element) :
    (rankNonzeroLimitAt x).Realize free bound ↔ setNonzeroLimit (Sum.elim free bound x).val := by
  rw [rankNonzeroLimitAt, BoundedFormula.realize_relabel]
  change rankNonzeroLimitFormula.Realize (Sum.elim free bound ∘ ![x]) ↔ _
  have tuple : Sum.elim free bound ∘ ![x] = ![Sum.elim free bound x] := by
    funext i; fin_cases i; rfl
  rw [tuple, M.nonzeroLimitFormula_absolute]

theorem firstLimitFormula_absolute (M : TransitiveClass.{u}) (x : M.Element) :
    rankFirstLimitFormula.Realize ![x] ↔ setFirstLimit x.val := by
  change (rankNonzeroLimitFormula ⊓ _).Realize ![x] ↔ _
  simp only [Formula.Realize, BoundedFormula.realize_inf]
  change (rankNonzeroLimitFormula.Realize ![x] ∧ _) ↔ _
  rw [M.nonzeroLimitFormula_absolute]
  have lower : (∀ z : M.Element, z.val ∈ x.val → ¬setNonzeroLimit z.val) ↔
      ∀ z ∈ x.val, ¬setNonzeroLimit z := by
    constructor
    · exact fun h z hz => h (M.member x z hz) hz
    · exact fun h z hz => h z.val hz
  simpa [setFirstLimit, BoundedFormula.Realize, M.memAt_realize,
    M.nonzeroLimitAt_absolute, Fin.snoc] using and_congr Iff.rfl lower

/-- Initiality uses only surjections whose set graphs belong to M. -/
def InternalInitial (M : TransitiveClass.{u}) (k : M.Element) : Prop :=
  ZFSet.IsOrdinal k.val ∧ ∀ a : M.Element, a.val ∈ k.val → ∀ f : M.Element,
    ¬(ZFSet.IsFunc a.val k.val f.val ∧ setGraphOnto f.val a.val k.val)

def NoSmallCofinal (M : TransitiveClass.{u}) (k : M.Element) : Prop :=
  ∀ a : M.Element, a.val ∈ k.val → ∀ f : M.Element,
    ¬(ZFSet.IsFunc a.val k.val f.val ∧ setGraphCofinal f.val a.val k.val)

/-- Initiality and the short-cofinal-graph test. Its intended regular-cardinal
use is at uncountable initial ordinals; by itself this predicate also allows
finite initial ordinals. `InternalInaccessible` includes uncountability. -/
def InternalRegular (M : TransitiveClass.{u}) (k : M.Element) : Prop :=
  M.InternalInitial k ∧ M.NoSmallCofinal k

def InternalPowerset (M : TransitiveClass.{u}) (p x : M.Element) : Prop :=
  ∀ z : M.Element, z.val ∈ p.val ↔ z.val ⊆ x.val

/-- For an initial uncountable ordinal this is the strong-limit condition:
no internally available power set of a smaller ordinal surjects onto k. -/
def InternalStrongLimit (M : TransitiveClass.{u}) (k : M.Element) : Prop :=
  ∀ a : M.Element, a.val ∈ k.val → ∀ p : M.Element, M.InternalPowerset p a →
    ∀ f : M.Element, ¬(ZFSet.IsFunc p.val k.val f.val ∧ setGraphOnto f.val p.val k.val)

def InternalUncountable (M : TransitiveClass.{u}) (k : M.Element) : Prop :=
  ∃ w : M.Element, ZFSet.IsOrdinal w.val ∧ setFirstLimit w.val ∧ w.val ∈ k.val

def InternalInaccessible (M : TransitiveClass.{u}) (k : M.Element) : Prop :=
  M.InternalInitial k ∧ M.InternalUncountable k ∧ M.NoSmallCofinal k ∧ M.InternalStrongLimit k

end TransitiveClass

def internalInitialFormula : RankPredicateFormula 0 1 :=
  (rankPredicateAtom rankOrdinalFormula ![0]).and
    (.all ((RankPredicateFormula.member 1 0).imp
      (.all ((rankPredicateAtom rankFunctionFormula ![2, 1, 0]).and
        (rankPredicateAtom rankOntoFormula ![2, 1, 0])).not)))

def noSmallCofinalFormula : RankPredicateFormula 0 1 :=
  .all ((RankPredicateFormula.member 1 0).imp
    (.all ((rankPredicateAtom rankFunctionFormula ![2, 1, 0]).and
      (rankPredicateAtom rankCofinalFormula ![2, 1, 0])).not))

def internalStrongLimitFormula : RankPredicateFormula 0 1 :=
  .all ((RankPredicateFormula.member 1 0).imp
    (.all ((rankPredicateAtom rankPowersetFormula ![2, 1]).imp
      (.all ((rankPredicateAtom rankFunctionFormula ![3, 2, 0]).and
        (rankPredicateAtom rankOntoFormula ![3, 2, 0])).not))))

def internalUncountableFormula : RankPredicateFormula 0 1 :=
  ((rankPredicateAtom rankOrdinalFormula ![1]).and
    ((rankPredicateAtom rankFirstLimitFormula ![1]).and (.member 1 0))).ex

def internalInaccessibleFormula : RankPredicateFormula 0 1 :=
  internalInitialFormula.and (internalUncountableFormula.and
    (noSmallCofinalFormula.and internalStrongLimitFormula))

namespace TransitiveClass

private theorem ordinalValues (M : TransitiveClass.{u}) (v : Fin 1 → M.Element) :
    rankOrdinalFormula.Realize v ↔ ZFSet.IsOrdinal (v 0).val := by
  have tuple : v = ![v 0] := by funext i; fin_cases i; rfl
  rw [tuple, M.ordinalFormula_realize]
  rfl

private theorem functionValues (M : TransitiveClass.{u}) (v : Fin 3 → M.Element) :
    rankFunctionFormula.Realize v ↔ ZFSet.IsFunc (v 1).val (v 2).val (v 0).val := by
  have tuple : v = ![v 0, v 1, v 2] := by funext i; fin_cases i <;> rfl
  rw [tuple, M.functionFormula_realize, M.function_absolute]
  rfl

private theorem ontoValues (M : TransitiveClass.{u}) (v : Fin 3 → M.Element) :
    rankOntoFormula.Realize v ↔ setGraphOnto (v 0).val (v 1).val (v 2).val := by
  have tuple : v = ![v 0, v 1, v 2] := by funext i; fin_cases i <;> rfl
  rw [tuple, M.ontoFormula_absolute]
  rfl

private theorem cofinalValues (M : TransitiveClass.{u}) (v : Fin 3 → M.Element) :
    rankCofinalFormula.Realize v ↔ setGraphCofinal (v 0).val (v 1).val (v 2).val := by
  have tuple : v = ![v 0, v 1, v 2] := by funext i; fin_cases i <;> rfl
  rw [tuple, M.cofinalFormula_absolute]
  rfl

private theorem powersetValues (M : TransitiveClass.{u}) (v : Fin 2 → M.Element) :
    rankPowersetFormula.Realize v ↔ M.InternalPowerset (v 0) (v 1) := by
  have tuple : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  rw [tuple, M.powersetFormula_realize]
  rfl

private theorem firstLimitValues (M : TransitiveClass.{u}) (v : Fin 1 → M.Element) :
    rankFirstLimitFormula.Realize v ↔ setFirstLimit (v 0).val := by
  have tuple : v = ![v 0] := by funext i; fin_cases i; rfl
  rw [tuple, M.firstLimitFormula_absolute]
  rfl

theorem internalInitialFormula_realize (M : TransitiveClass.{u}) (k : M.Element) :
    M.realize internalInitialFormula ![k] ↔ M.InternalInitial k := by
  simp [internalInitialFormula, M.realize_and, M.realize_not, M.realize_atom,
    realize, ordinalValues, functionValues, ontoValues, InternalInitial, Function.comp_def, Fin.snoc]

theorem noSmallCofinalFormula_realize (M : TransitiveClass.{u}) (k : M.Element) :
    M.realize noSmallCofinalFormula ![k] ↔ M.NoSmallCofinal k := by
  simp [noSmallCofinalFormula, M.realize_and, M.realize_not, M.realize_atom,
    realize, functionValues, cofinalValues, NoSmallCofinal, Function.comp_def, Fin.snoc]

theorem internalStrongLimitFormula_realize (M : TransitiveClass.{u}) (k : M.Element) :
    M.realize internalStrongLimitFormula ![k] ↔ M.InternalStrongLimit k := by
  simp [internalStrongLimitFormula, M.realize_and, M.realize_not, M.realize_atom,
    realize, functionValues, powersetValues, ontoValues, InternalStrongLimit, Function.comp_def, Fin.snoc]

theorem internalUncountableFormula_realize (M : TransitiveClass.{u}) (k : M.Element) :
    M.realize internalUncountableFormula ![k] ↔ M.InternalUncountable k := by
  simp [internalUncountableFormula, M.realize_ex, M.realize_and, M.realize_atom,
    realize, ordinalValues, firstLimitValues,
    InternalUncountable, Function.comp_def]

theorem internalInaccessibleFormula_realize (M : TransitiveClass.{u}) (k : M.Element) :
    M.realize internalInaccessibleFormula ![k] ↔ M.InternalInaccessible k := by
  rw [internalInaccessibleFormula, M.realize_and, M.internalInitialFormula_realize,
    M.realize_and, M.internalUncountableFormula_realize, M.realize_and,
    M.noSmallCofinalFormula_realize, M.internalStrongLimitFormula_realize]
  rfl

theorem ElementaryMap.internalInaccessible_iff {M N : TransitiveClass.{u}}
    (j : M.ElementaryMap N) (k : M.Element) :
    N.InternalInaccessible (j k) ↔ M.InternalInaccessible k := by
  have h := j.realize_iff internalInaccessibleFormula ![k]
  have tuple : j ∘ ![k] = ![j k] := by funext i; fin_cases i; rfl
  rw [tuple, N.internalInaccessibleFormula_realize, M.internalInaccessibleFormula_realize] at h
  exact h

end TransitiveClass
end IBLP
