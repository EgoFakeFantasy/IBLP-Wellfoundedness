import IBLP.Model.Pair
import IBLP.Model.Ordinals
import FullMarkedBLP.RankGraphClosure

namespace IBLP
open FullMarkedBLP FirstOrder Language
universe u

def modelInsertFormula : membershipLanguage.Formula (Fin 3) :=
  .all ((rankMemAt (.inr 0) (.inl 0)).iff
    ((BoundedFormula.equal (.var (.inr 0)) (.var (.inl 1))) ⊔ rankMemAt (.inr 0) (.inl 2)))

theorem TransitiveClass.insertFormula_realize (M : TransitiveClass.{u}) (z x y : M.Element) :
    modelInsertFormula.Realize ![z, x, y] ↔ z.val = insert x.val y.val := by
  have sem : modelInsertFormula.Realize ![z, x, y] ↔
      ∀ w : M.Element, w.val ∈ z.val ↔ w = x ∨ w.val ∈ y.val := by
    classical
    simp [modelInsertFormula, Formula.Realize, BoundedFormula.Realize,
      M.memAt_realize, Fin.snoc, imp_iff_not_or]
  rw [sem]
  constructor
  · intro h
    apply ZFSet.ext
    intro w
    rw [ZFSet.mem_insert_iff]
    constructor
    · intro hw
      rcases (h (M.member z w hw)).mp hw with eq | mem
      · exact Or.inl (congrArg Subtype.val eq)
      · exact Or.inr mem
    · rintro (eq | mem)
      · subst w
        exact (h x).mpr (Or.inl rfl)
      · exact (h (M.member y w mem)).mpr (Or.inr mem)
  · intro eq w
    rw [eq, ZFSet.mem_insert_iff]
    exact or_congr Subtype.val_inj Iff.rfl

theorem ModelStage.insert_exists (stage : ModelStage.{u}) (x y : stage.model.Element) :
    ∃ z : stage.model.Element, z.val = insert x.val y.val := by
  let phi : RankPredicateFormula 0 3 := rankPredicateAtom modelInsertFormula ![2, 0, 1]
  have sem (M : TransitiveClass.{u}) (v : Fin 2 → M.Element) (z : M.Element) :
      M.realize phi (Fin.snoc v z) ↔ z.val = insert (v 0).val (v 1).val := by
    rw [show phi = rankPredicateAtom modelInsertFormula ![2, 0, 1] from rfl, M.realize_atom]
    have tuple : Fin.snoc v z ∘ ![2, 0, 1] = ![z, v 0, v 1] := by
      funext i; fin_cases i <;> rfl
    rw [tuple, M.insertFormula_realize]
  have initial : ∀ v, ∃ z, universeClass.{u}.toTransitiveClass.realize phi (Fin.snoc v z) := by
    intro v
    exact ⟨⟨insert (v 0).val (v 1).val, Set.mem_univ _⟩, (sem _ _ _).mpr rfl⟩
  obtain ⟨z, hz⟩ := stage.transfer_exists phi initial ![x, y]
  exact ⟨z, (sem _ _ _).mp hz⟩

noncomputable def ModelStage.insert (stage : ModelStage.{u}) (x y : stage.model.Element) :
    stage.model.Element := (stage.insert_exists x y).choose

theorem ModelStage.insert_val (stage : ModelStage.{u}) (x y : stage.model.Element) :
    (stage.insert x y).val = Insert.insert x.val y.val := (stage.insert_exists x y).choose_spec

noncomputable def ModelStage.finiteSet (stage : ModelStage.{u}) : List stage.model.Element → stage.model.Element
  | [] => stage.ordinal 0
  | x :: xs => stage.insert x (stage.finiteSet xs)

theorem ModelStage.mem_finiteSet (stage : ModelStage.{u}) (xs : List stage.model.Element) (z : ZFSet.{u}) :
    z ∈ (stage.finiteSet xs).val ↔ ∃ x ∈ xs, x.val = z := by
  induction xs with
  | nil => simp [finiteSet, ordinal]
  | cons x xs ih =>
    rw [finiteSet, stage.insert_val, ZFSet.mem_insert_iff, ih]
    simp only [List.mem_cons]
    constructor
    · rintro (eq | ⟨y, hy, eq⟩)
      · exact ⟨x, Or.inl rfl, eq.symm⟩
      · exact ⟨y, Or.inr hy, eq⟩
    · rintro ⟨y, eq | hy, hz⟩
      · subst y; exact Or.inl hz.symm
      · exact Or.inr ⟨y, hy, hz⟩

noncomputable def ModelStage.finiteRange (stage : ModelStage.{u}) {n : Nat}
    (values : Fin n → stage.model.Element) : stage.model.Element := stage.finiteSet (List.ofFn values)

theorem ModelStage.finiteRange_val (stage : ModelStage.{u}) {n : Nat}
    (values : Fin n → stage.model.Element) :
    (stage.finiteRange values).val = ZFSet.range (fun i => (values i).val) := by
  apply ZFSet.ext
  intro z
  rw [finiteRange, stage.mem_finiteSet, ZFSet.mem_range]
  simp only [List.mem_ofFn]
  constructor
  · rintro ⟨x, ⟨i, rfl⟩, eq⟩
    exact ⟨i, eq⟩
  · rintro ⟨i, eq⟩
    exact ⟨values i, ⟨i, rfl⟩, eq⟩

/-- An arbitrary external finite family of model elements has its complete
finite function graph in M, by finite set operations alone. -/
noncomputable def ModelStage.finiteGraph (stage : ModelStage.{u}) {n : Nat}
    (values : Fin n → stage.model.Element) : stage.model.Element :=
  stage.finiteRange (fun i => stage.orderedPair (stage.ordinal (i.val : Ordinal.{u})) (values i))

theorem ModelStage.finiteGraph_val (stage : ModelStage.{u}) {n : Nat}
    (values : Fin n → stage.model.Element) :
    (stage.finiteGraph values).val =
      ZFSet.range (fun i : Fin n => ZFSet.pair (i.val : Ordinal.{u}).toZFSet (values i).val) := by
  rw [finiteGraph, stage.finiteRange_val]
  congr 1
  funext i
  exact stage.orderedPair_val _ _

theorem ModelStage.finiteGraph_edge_iff (stage : ModelStage.{u}) {n : Nat}
    (values : Fin n → stage.model.Element) (a b : ZFSet.{u}) :
    ZFSet.pair a b ∈ (stage.finiteGraph values).val ↔
      ∃ i : Fin n, (i.val : Ordinal.{u}).toZFSet = a ∧ (values i).val = b := by
  rw [stage.finiteGraph_val, ZFSet.mem_range]
  simp only [ZFSet.pair_inj]

end IBLP
