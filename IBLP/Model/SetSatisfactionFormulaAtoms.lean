import IBLP.Model.FiniteSets
import IBLP.Model.GraphOperations
import FullMarkedBLP.RankAssignmentFormula

namespace IBLP
open FullMarkedBLP FirstOrder Language
universe u

/-- The same nested Kuratowski tuple used by the fixed syntax tables. -/
noncomputable def setTuple : {n : Nat} → (Fin n → ZFSet.{u}) → ZFSet.{u}
  | 0, _ => ∅
  | n + 1, xs => ZFSet.pair (xs 0) (setTuple (fun i : Fin n => xs i.succ))

noncomputable def ModelStage.setTuple (stage : ModelStage.{u}) :
    {n : Nat} → (Fin n → stage.model.Element) → stage.model.Element
  | 0, _ => stage.ordinal 0
  | n + 1, xs => stage.orderedPair (xs 0) (stage.setTuple (fun i : Fin n => xs i.succ))

theorem ModelStage.setTuple_val (stage : ModelStage.{u}) {n : Nat}
    (xs : Fin n → stage.model.Element) :
    (stage.setTuple xs).val = IBLP.setTuple (fun i => (xs i).val) := by
  induction n with
  | zero => simp [ModelStage.setTuple, ModelStage.ordinal, IBLP.setTuple]
  | succ n ih =>
    change (stage.orderedPair _ _).val = _
    rw [stage.orderedPair_val, ih]
    rfl

theorem setTuple_nat {n : Nat} (xs : Fin n → Nat) :
    setTuple (fun i => (xs i : Ordinal.{u}).toZFSet) = zfNatTuple xs := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [setTuple, zfNatTuple, ih]

namespace TransitiveClass

theorem pure_iff_realize (M : TransitiveClass.{u}) {n : Nat}
    (p q : RankPredicateFormula 0 n) (v : Fin n → M.Element) :
    M.realize (p.iff q) v ↔ (M.realize p v ↔ M.realize q v) := by
  rw [RankPredicateFormula.iff, M.realize_and]
  exact iff_def.symm

theorem pure_or_realize (M : TransitiveClass.{u}) {n : Nat}
    (p q : RankPredicateFormula 0 n) (v : Fin n → M.Element) :
    M.realize (p.or q) v ↔ M.realize p v ∨ M.realize q v := by
  classical
  simp only [RankPredicateFormula.or, TransitiveClass.realize, M.realize_not]
  tauto

theorem setOrderedPairAtom_realize (M : TransitiveClass.{u}) {n : Nat}
    (p x y : Fin n) (v : Fin n → M.Element) :
    M.realize (rankFormulaOrderedPair p x y) v ↔
      (v p).val = ZFSet.pair (v x).val (v y).val := by
  rw [rankFormulaOrderedPair, M.realize_atom, rankMapTriple,
    M.orderedPairFormula_realize, M.orderedPair_absolute]

theorem setFunctionAtom_realize (M : TransitiveClass.{u}) {n : Nat}
    (graph domain range : Fin n) (v : Fin n → M.Element) :
    M.realize (rankFormulaFunction graph domain range) v ↔
      ZFSet.IsFunc (v domain).val (v range).val (v graph).val := by
  rw [rankFormulaFunction, M.realize_atom, rankMapTriple,
    M.functionFormula_realize, M.function_absolute]

theorem setGraphAtom_realize (M : TransitiveClass.{u}) {n : Nat}
    (graph x y : Fin n) (v : Fin n → M.Element) :
    M.realize (rankFormulaGraphApplies graph x y) v ↔
      ZFSet.pair (v x).val (v y).val ∈ (v graph).val :=
  M.graphFormulaAtom_realize _ _ _ _

theorem setEmptyAtom_realize (M : TransitiveClass.{u}) {n : Nat}
    (x : Fin n) (v : Fin n → M.Element) :
    M.realize (rankFormulaEmpty x) v ↔ (v x).val = ∅ := by
  rw [rankFormulaEmpty, M.realize_atom, rankMapSingle]
  have sem : rankEmptyFormula.Realize ![v x] ↔ ∀ w : M.Element, w.val ∉ (v x).val := by
    simp [rankEmptyFormula, Formula.Realize, BoundedFormula.Realize, M.memAt_realize, Fin.snoc]
  rw [sem]
  constructor
  · intro h
    apply ZFSet.ext
    intro w
    simp only [ZFSet.notMem_empty, iff_false]
    exact fun hw => h (M.member (v x) w hw) hw
  · intro same w
    rw [same]
    exact ZFSet.notMem_empty _

end TransitiveClass

theorem setTupleFormula_realize (stage : ModelStage.{u}) {k n : Nat}
    (tuple : Fin n) (entries : Fin k → Fin n) (v : Fin n → stage.model.Element) :
    stage.model.realize (rankFormulaTuple tuple entries) v ↔
      (v tuple).val = setTuple (fun i => (v (entries i)).val) := by
  induction k generalizing n with
  | zero => exact stage.model.setEmptyAtom_realize tuple v
  | succ k ih =>
    simp only [rankFormulaTuple, stage.model.realize_ex, stage.model.realize_and,
      stage.model.setOrderedPairAtom_realize, ih, Fin.snoc_castSucc, Fin.snoc_last]
    constructor
    · rintro ⟨tail, pair, same⟩
      rw [same] at pair
      exact pair
    · intro same
      refine ⟨stage.setTuple (fun i : Fin k => v (entries i.succ)), ?_, stage.setTuple_val _⟩
      rw [stage.setTuple_val]
      exact same

theorem setTableFormula_realize (stage : ModelStage.{u}) {k n : Nat}
    (book : Fin n) (entries : Fin k → Fin n) (v : Fin n → stage.model.Element) :
    stage.model.realize (rankFormulaTupleMem book entries) v ↔
      setTuple (fun i => (v (entries i)).val) ∈ (v book).val := by
  simp only [rankFormulaTupleMem, stage.model.realize_ex, stage.model.realize_and,
    TransitiveClass.realize, setTupleFormula_realize, Fin.snoc_castSucc, Fin.snoc_last]
  constructor
  · rintro ⟨tuple, mem, same⟩
    rwa [same] at mem
  · intro mem
    exact ⟨stage.setTuple (fun i => v (entries i)), by simpa only [stage.setTuple_val] using mem,
      stage.setTuple_val _⟩

theorem setAppendFormula_realize (stage : ModelStage.{u}) {n : Nat}
    (old new index value : Fin n) (v : Fin n → stage.model.Element) :
    stage.model.realize (rankFormulaAppend old new index value) v ↔
      (v new).val = (v old).val ∪ {ZFSet.pair (v index).val (v value).val} := by
  simp only [rankFormulaAppend, TransitiveClass.realize, stage.model.pure_iff_realize,
    stage.model.pure_or_realize, stage.model.setOrderedPairAtom_realize,
    Fin.snoc_last, Fin.snoc_castSucc]
  constructor
  · intro h
    apply ZFSet.ext
    intro p
    rw [ZFSet.mem_union, ZFSet.mem_singleton]
    constructor
    · intro hp
      exact (h (stage.model.member (v new) p hp)).mp hp
    · rintro (hp | hp)
      · exact (h (stage.model.member (v old) p hp)).mpr (Or.inl hp)
      · subst p
        have same := stage.orderedPair_val (v index) (v value)
        exact same ▸ (h (stage.orderedPair (v index) (v value))).mpr (Or.inr same)
  · intro same p
    rw [same, ZFSet.mem_union, ZFSet.mem_singleton]

end IBLP
