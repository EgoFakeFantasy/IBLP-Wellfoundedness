import IBLP.Model.SetSatisfactionFormulaAtoms

namespace IBLP
open FullMarkedBLP FirstOrder Language
universe u

def SetTableHolds {M : TransitiveClass.{u}} {n : Nat}
    (book : M.Element) (entries : Fin n → M.Element) : Prop :=
  setTuple (fun i => (entries i).val) ∈ book.val

def SetAssignmentAtCode (M : TransitiveClass.{u}) (arityBook D code assignment : M.Element) : Prop :=
  ∃ arity : M.Element, SetTableHolds arityBook ![code, arity] ∧
    ZFSet.IsFunc arity.val D.val assignment.val

def setValidAssignment {n : Nat} (book domain code assignment : Fin n) : RankPredicateFormula 0 n :=
  ((rankFormulaTupleMem book.castSucc ![code.castSucc, Fin.last n]).and
    (rankFormulaFunction assignment.castSucc (Fin.last n) domain.castSucc)).ex

theorem setValidAssignment_realize (stage : ModelStage.{u}) {n : Nat}
    (book domain code assignment : Fin n) (v : Fin n → stage.model.Element) :
    stage.model.realize (setValidAssignment book domain code assignment) v ↔
      SetAssignmentAtCode stage.model (v book) (v domain) (v code) (v assignment) := by
  simp only [setValidAssignment, stage.model.realize_ex, stage.model.realize_and,
    setTableFormula_realize stage, stage.model.setFunctionAtom_realize,
    Fin.snoc_castSucc, Fin.snoc_last, SetAssignmentAtCode, SetTableHolds]
  simp [setTuple, Fin.snoc]

/-- Set-only recursion over one set D. Support excludes all malformed or
out-of-domain entries; the remaining five fields are the syntax constructors. -/
structure SetCodedTruthConditions (M : TransitiveClass.{u})
    (books : Fin 6 → M.Element) (D truth : M.Element) : Prop where
  support : ∀ p : M.Element, p.val ∈ truth.val →
    ∃ code assignment : M.Element, p.val = ZFSet.pair code.val assignment.val ∧
      SetAssignmentAtCode M (books 0) D code assignment
  falsum : ∀ code assignment, SetAssignmentAtCode M (books 0) D code assignment →
    SetTableHolds (books 1) ![code] → ZFSet.pair code.val assignment.val ∉ truth.val
  equal : ∀ code assignment i j x y : M.Element, SetAssignmentAtCode M (books 0) D code assignment →
    SetTableHolds (books 2) ![code, i, j] →
    ZFSet.pair i.val x.val ∈ assignment.val → ZFSet.pair j.val y.val ∈ assignment.val →
    (ZFSet.pair code.val assignment.val ∈ truth.val ↔ x = y)
  member : ∀ code assignment i j x y : M.Element, SetAssignmentAtCode M (books 0) D code assignment →
    SetTableHolds (books 3) ![code, i, j] →
    ZFSet.pair i.val x.val ∈ assignment.val → ZFSet.pair j.val y.val ∈ assignment.val →
    (ZFSet.pair code.val assignment.val ∈ truth.val ↔ x.val ∈ y.val)
  imp : ∀ code assignment p q : M.Element, SetAssignmentAtCode M (books 0) D code assignment →
    SetTableHolds (books 4) ![code, p, q] →
    (ZFSet.pair code.val assignment.val ∈ truth.val ↔
      (ZFSet.pair p.val assignment.val ∈ truth.val → ZFSet.pair q.val assignment.val ∈ truth.val))
  all : ∀ code assignment p arity : M.Element, SetTableHolds (books 0) ![code, arity] →
    ZFSet.IsFunc arity.val D.val assignment.val → SetTableHolds (books 5) ![code, p] →
    (ZFSet.pair code.val assignment.val ∈ truth.val ↔ ∀ x new : M.Element,
      x.val ∈ D.val → new.val = assignment.val ∪ {ZFSet.pair arity.val x.val} →
        ZFSet.pair p.val new.val ∈ truth.val)

def setSatSupportMatrix : RankPredicateFormula 0 8 :=
  .all ((RankPredicateFormula.member 8 7).imp
    (((rankFormulaOrderedPair 8 9 10).and (setValidAssignment 0 6 9 10)).ex.ex))

def setSatFalseMatrix : RankPredicateFormula 0 8 :=
  let body : RankPredicateFormula 0 10 :=
    .imp (setValidAssignment 0 6 8 9)
      (.imp (rankFormulaTupleMem 1 ![8]) (rankFormulaGraphApplies 7 8 9).not)
  body.all.all

def setSatEqualMatrix : RankPredicateFormula 0 8 :=
  let body : RankPredicateFormula 0 14 :=
    .imp (setValidAssignment 0 6 8 9)
      (.imp (rankFormulaTupleMem 2 ![8, 10, 11])
        (.imp (rankFormulaGraphApplies 9 10 12) (.imp (rankFormulaGraphApplies 9 11 13)
          ((rankFormulaGraphApplies 7 8 9).iff (.equal 12 13)))))
  body.all.all.all.all.all.all

def setSatMemberMatrix : RankPredicateFormula 0 8 :=
  let body : RankPredicateFormula 0 14 :=
    .imp (setValidAssignment 0 6 8 9)
      (.imp (rankFormulaTupleMem 3 ![8, 10, 11])
        (.imp (rankFormulaGraphApplies 9 10 12) (.imp (rankFormulaGraphApplies 9 11 13)
          ((rankFormulaGraphApplies 7 8 9).iff (.member 12 13)))))
  body.all.all.all.all.all.all

def setSatImpMatrix : RankPredicateFormula 0 8 :=
  let body : RankPredicateFormula 0 12 :=
    .imp (setValidAssignment 0 6 8 9) (.imp (rankFormulaTupleMem 4 ![8, 10, 11])
      ((rankFormulaGraphApplies 7 8 9).iff
        (.imp (rankFormulaGraphApplies 7 10 9) (rankFormulaGraphApplies 7 11 9))))
  body.all.all.all.all

def setSatAllMatrix : RankPredicateFormula 0 8 :=
  let extension : RankPredicateFormula 0 14 :=
    .imp (.member 12 6) (.imp (rankFormulaAppend 9 13 11 12) (rankFormulaGraphApplies 7 10 13))
  let body : RankPredicateFormula 0 12 :=
    .imp (rankFormulaTupleMem 0 ![8, 11]) (.imp (rankFormulaFunction 9 11 6)
      (.imp (rankFormulaTupleMem 5 ![8, 10])
        ((rankFormulaGraphApplies 7 8 9).iff extension.all.all)))
  body.all.all.all.all

/-- A single fixed finite pure membership formula, with six syntax table
parameters and the two actual sets D and T. There is no formula scheme or
truth predicate in this object-language expression. -/
def setSatisfactionMatrix : RankPredicateFormula 0 8 :=
  setSatSupportMatrix.and (setSatFalseMatrix.and (setSatEqualMatrix.and
    (setSatMemberMatrix.and (setSatImpMatrix.and setSatAllMatrix))))

def setSatisfactionFormula : membershipLanguage.Formula (Fin 8) :=
  rankPredicateToFormula setSatisfactionMatrix

theorem setSatisfactionMatrix_realize (stage : ModelStage.{u})
    (books : Fin 6 → stage.model.Element) (D truth : stage.model.Element) :
    stage.model.realize setSatisfactionMatrix (Fin.snoc (Fin.snoc books D) truth) ↔
      SetCodedTruthConditions stage.model books D truth := by
  have support : stage.model.realize setSatSupportMatrix (Fin.snoc (Fin.snoc books D) truth) ↔
      ∀ p : stage.model.Element, p.val ∈ truth.val →
        ∃ code assignment : stage.model.Element, p.val = ZFSet.pair code.val assignment.val ∧
          SetAssignmentAtCode stage.model (books 0) D code assignment := by
    simp [setSatSupportMatrix, TransitiveClass.realize, stage.model.realize_ex, stage.model.realize_and,
      stage.model.setOrderedPairAtom_realize, setValidAssignment_realize stage, Fin.snoc]
  have falseClause : stage.model.realize setSatFalseMatrix (Fin.snoc (Fin.snoc books D) truth) ↔
      ∀ code assignment, SetAssignmentAtCode stage.model (books 0) D code assignment →
        SetTableHolds (books 1) ![code] → ZFSet.pair code.val assignment.val ∉ truth.val := by
    simp [setSatFalseMatrix, TransitiveClass.realize, stage.model.realize_not,
      setValidAssignment_realize stage, setTableFormula_realize stage, stage.model.setGraphAtom_realize,
      SetTableHolds, setTuple, Fin.snoc]
  have equalClause : stage.model.realize setSatEqualMatrix (Fin.snoc (Fin.snoc books D) truth) ↔
      ∀ code assignment i j x y : stage.model.Element, SetAssignmentAtCode stage.model (books 0) D code assignment →
        SetTableHolds (books 2) ![code, i, j] →
        ZFSet.pair i.val x.val ∈ assignment.val → ZFSet.pair j.val y.val ∈ assignment.val →
        (ZFSet.pair code.val assignment.val ∈ truth.val ↔ x = y) := by
    simp [setSatEqualMatrix, TransitiveClass.realize, stage.model.pure_iff_realize,
      setValidAssignment_realize stage, setTableFormula_realize stage, stage.model.setGraphAtom_realize,
      SetTableHolds, setTuple, Fin.snoc]
  have memberClause : stage.model.realize setSatMemberMatrix (Fin.snoc (Fin.snoc books D) truth) ↔
      ∀ code assignment i j x y : stage.model.Element, SetAssignmentAtCode stage.model (books 0) D code assignment →
        SetTableHolds (books 3) ![code, i, j] →
        ZFSet.pair i.val x.val ∈ assignment.val → ZFSet.pair j.val y.val ∈ assignment.val →
        (ZFSet.pair code.val assignment.val ∈ truth.val ↔ x.val ∈ y.val) := by
    simp [setSatMemberMatrix, TransitiveClass.realize, stage.model.pure_iff_realize,
      setValidAssignment_realize stage, setTableFormula_realize stage, stage.model.setGraphAtom_realize,
      SetTableHolds, setTuple, Fin.snoc]
  have impClause : stage.model.realize setSatImpMatrix (Fin.snoc (Fin.snoc books D) truth) ↔
      ∀ code assignment p q : stage.model.Element, SetAssignmentAtCode stage.model (books 0) D code assignment →
        SetTableHolds (books 4) ![code, p, q] →
        (ZFSet.pair code.val assignment.val ∈ truth.val ↔
          (ZFSet.pair p.val assignment.val ∈ truth.val → ZFSet.pair q.val assignment.val ∈ truth.val)) := by
    simp [setSatImpMatrix, TransitiveClass.realize, stage.model.pure_iff_realize,
      setValidAssignment_realize stage, setTableFormula_realize stage, stage.model.setGraphAtom_realize,
      SetTableHolds, setTuple, Fin.snoc]
  have allClause : stage.model.realize setSatAllMatrix (Fin.snoc (Fin.snoc books D) truth) ↔
      ∀ code assignment p arity : stage.model.Element, SetTableHolds (books 0) ![code, arity] →
        ZFSet.IsFunc arity.val D.val assignment.val → SetTableHolds (books 5) ![code, p] →
        (ZFSet.pair code.val assignment.val ∈ truth.val ↔ ∀ x new : stage.model.Element,
          x.val ∈ D.val → new.val = assignment.val ∪ {ZFSet.pair arity.val x.val} →
            ZFSet.pair p.val new.val ∈ truth.val) := by
    simp [setSatAllMatrix, TransitiveClass.realize, stage.model.pure_iff_realize,
      stage.model.setFunctionAtom_realize, setTableFormula_realize stage, stage.model.setGraphAtom_realize,
      setAppendFormula_realize stage, SetTableHolds, setTuple, Fin.snoc]
  rw [setSatisfactionMatrix, stage.model.realize_and, stage.model.realize_and, stage.model.realize_and, stage.model.realize_and,
    stage.model.realize_and, support, falseClause, equalClause, memberClause, impClause, allClause]
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩,
    fun h => ⟨h.support, h.falsum, h.equal, h.member, h.imp, h.all⟩⟩

theorem setSatisfactionFormula_realize (stage : ModelStage.{u})
    (books : Fin 6 → stage.model.Element) (D truth : stage.model.Element) :
    setSatisfactionFormula.Realize (Fin.snoc (Fin.snoc books D) truth) ↔
      SetCodedTruthConditions stage.model books D truth := by
  rw [setSatisfactionFormula, ← stage.model.realize_toFormula, setSatisfactionMatrix_realize]

end IBLP



