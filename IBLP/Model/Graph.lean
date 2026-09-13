import IBLP.Model.Pair
import IBLP.Model.Ordinals
import FullMarkedBLP.RankFunctionFormula

namespace IBLP
open FullMarkedBLP FirstOrder Language
universe u

namespace TransitiveClass

theorem orderedPairAt_realize (M : TransitiveClass.{u}) {alpha : Type} {n : Nat}
    (z x y : alpha ⊕ Fin n) (free : alpha → M.Element) (bound : Fin n → M.Element) :
    (rankOrderedPairAt z x y).Realize free bound ↔
      M.IsOrderedPair (Sum.elim free bound z) (Sum.elim free bound x) (Sum.elim free bound y) := by
  simp [rankOrderedPairAt, BoundedFormula.realize_relabel, rankOrderedPairFormula,
    BoundedFormula.realize_ex, BoundedFormula.realize_inf, M.unorderedPairAt_realize,
    IsOrderedPair, Function.comp_def, Fin.snoc]
  have he : (fun i : Fin n => bound (((Fin.castAdd 2 i).castLT
      (n := n + 1) (i.isLt.trans_le (Nat.le_succ n))).castLT i.isLt)) = bound := by
    funext i
    congr 1
  simp only [he]

def GraphApplies (M : TransitiveClass.{u}) (f x y : M.Element) : Prop :=
  ∃ p : M.Element, p.val ∈ f.val ∧ M.IsOrderedPair p x y

theorem graphApplies_absolute (M : TransitiveClass.{u}) (f x y : M.Element) :
    M.GraphApplies f x y ↔ ZFSet.pair x.val y.val ∈ f.val := by
  constructor
  · rintro ⟨p, hp, he⟩
    rwa [(M.orderedPair_absolute _ _ _).mp he] at hp
  · intro hp
    exact ⟨M.member f _ hp, hp, (M.orderedPair_absolute _ _ _).mpr rfl⟩

theorem graphAppliesFormula_realize (M : TransitiveClass.{u}) (f x y : M.Element) :
    rankGraphAppliesFormula.Realize ![f, x, y] ↔ M.GraphApplies f x y := by
  simp [rankGraphAppliesFormula, Formula.Realize, BoundedFormula.realize_ex,
    BoundedFormula.realize_inf, M.memAt_realize, M.orderedPairAt_realize, GraphApplies, Fin.snoc]

theorem graphAppliesAt_realize (M : TransitiveClass.{u}) {alpha : Type} {n : Nat}
    (f x y : alpha ⊕ Fin n) (free : alpha → M.Element) (bound : Fin n → M.Element) :
    (rankGraphAppliesAt f x y).Realize free bound ↔
      M.GraphApplies (Sum.elim free bound f) (Sum.elim free bound x) (Sum.elim free bound y) := by
  simp [rankGraphAppliesAt, BoundedFormula.realize_relabel, rankGraphAppliesFormula,
    BoundedFormula.realize_ex, BoundedFormula.realize_inf, M.memAt_realize,
    M.orderedPairAt_realize, GraphApplies, Function.comp_def, Fin.snoc]

def GraphBetween (M : TransitiveClass.{u}) (f x y : M.Element) : Prop :=
  ∀ p : M.Element, p.val ∈ f.val →
    ∃ a b : M.Element, a.val ∈ x.val ∧ b.val ∈ y.val ∧ M.IsOrderedPair p a b

theorem graphBetween_absolute (M : TransitiveClass.{u}) (f x y : M.Element) :
    M.GraphBetween f x y ↔ f.val ⊆ ZFSet.prod x.val y.val := by
  constructor
  · intro h p hp
    obtain ⟨a, b, ha, hb, he⟩ := h (M.member f p hp) hp
    exact ZFSet.mem_prod.mpr ⟨a.val, ha, b.val, hb, (M.orderedPair_absolute _ _ _).mp he⟩
  · intro h p hp
    obtain ⟨a, ha, b, hb, he⟩ := ZFSet.mem_prod.mp (h hp)
    exact ⟨M.member x a ha, M.member y b hb, ha, hb, (M.orderedPair_absolute _ _ _).mpr he⟩

theorem graphBetweenFormula_realize (M : TransitiveClass.{u}) (f x y : M.Element) :
    rankGraphBetweenFormula.Realize ![f, x, y] ↔ M.GraphBetween f x y := by
  simp [rankGraphBetweenFormula, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    M.memAt_realize, M.orderedPairAt_realize, GraphBetween, Fin.snoc]

def IsFunction (M : TransitiveClass.{u}) (f x y : M.Element) : Prop :=
  M.GraphBetween f x y ∧ ∀ a : M.Element, a.val ∈ x.val →
    ∃ b : M.Element, b.val ∈ y.val ∧ M.GraphApplies f a b ∧
      ∀ c : M.Element, M.GraphApplies f a c → c = b

theorem function_absolute (M : TransitiveClass.{u}) (f x y : M.Element) :
    M.IsFunction f x y ↔ ZFSet.IsFunc x.val y.val f.val := by
  constructor
  · rintro ⟨hg, ht⟩
    have hg' := (M.graphBetween_absolute f x y).mp hg
    refine ⟨hg', ?_⟩
    intro a ha
    obtain ⟨b, _, hab, hu⟩ := ht (M.member x a ha) ha
    refine ⟨b.val, (M.graphApplies_absolute _ _ _).mp hab, ?_⟩
    intro c hc
    have hcy := (ZFSet.pair_mem_prod.mp (hg' hc)).2
    exact congrArg Subtype.val (hu (M.member y c hcy) ((M.graphApplies_absolute _ _ _).mpr hc))
  · rintro ⟨hg, ht⟩
    refine ⟨(M.graphBetween_absolute f x y).mpr hg, ?_⟩
    intro a ha
    obtain ⟨b, hb, hu⟩ := ht a.val ha
    have hby := (ZFSet.pair_mem_prod.mp (hg hb)).2
    refine ⟨M.member y b hby, hby, (M.graphApplies_absolute _ _ _).mpr hb, ?_⟩
    intro c hc
    exact Subtype.ext (hu c.val ((M.graphApplies_absolute _ _ _).mp hc))

theorem functionFormula_realize (M : TransitiveClass.{u}) (f x y : M.Element) :
    rankFunctionFormula.Realize ![f, x, y] ↔ M.IsFunction f x y := by
  simp only [rankFunctionFormula, Formula.Realize, BoundedFormula.realize_inf]
  change (rankGraphBetweenFormula.Realize ![f, x, y] ∧ rankFunctionTotalFormula.Realize ![f, x, y]) ↔ _
  rw [M.graphBetweenFormula_realize]
  simp [Formula.Realize, rankFunctionTotalFormula, BoundedFormula.realize_all,
    BoundedFormula.Realize, M.memAt_realize, M.graphAppliesAt_realize, IsFunction, Fin.snoc]

theorem ElementaryMap.function_iff {M N : TransitiveClass.{u}} (j : M.ElementaryMap N)
    (f x y : M.Element) :
    ZFSet.IsFunc (j x).val (j y).val (j f).val ↔ ZFSet.IsFunc x.val y.val f.val := by
  have h := j.map_formula rankFunctionFormula ![f, x, y]
  have tuple : j ∘ ![f, x, y] = ![j f, j x, j y] := by funext i; fin_cases i <;> rfl
  rw [tuple, N.functionFormula_realize, M.functionFormula_realize,
    N.function_absolute, M.function_absolute] at h
  exact h

end TransitiveClass
end IBLP
