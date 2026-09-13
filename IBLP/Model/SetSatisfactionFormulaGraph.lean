import IBLP.Model.SetCodedAssignment
import IBLP.Model.BoundedGraph

namespace IBLP
open FullMarkedBLP FirstOrder Language
universe u

def SetGraphMapsAssignments (M : TransitiveClass.{u}) (graph left right : M.Element) : Prop :=
  ∀ i x y : M.Element, ZFSet.pair i.val x.val ∈ left.val →
    ZFSet.pair i.val y.val ∈ right.val → ZFSet.pair x.val y.val ∈ graph.val

def setAssignmentMapFormula {n : Nat} (graph left right : Fin n) : RankPredicateFormula 0 n :=
  let body : RankPredicateFormula 0 (n + 3) :=
    .imp (rankFormulaGraphApplies (left.castAdd 3) ((Fin.last n).castAdd 2)
      (Fin.last (n + 1)).castSucc)
      (.imp (rankFormulaGraphApplies (right.castAdd 3) ((Fin.last n).castAdd 2) (Fin.last (n + 2)))
        (rankFormulaGraphApplies (graph.castAdd 3) (Fin.last (n + 1)).castSucc (Fin.last (n + 2))))
  body.all.all.all

theorem setAssignmentMapFormula_realize (M : TransitiveClass.{u}) {n : Nat}
    (graph left right : Fin n) (v : Fin n → M.Element) :
    M.realize (setAssignmentMapFormula graph left right) v ↔
      SetGraphMapsAssignments M (v graph) (v left) (v right) := by
  simp only [setAssignmentMapFormula, TransitiveClass.realize, M.setGraphAtom_realize,
    Fin.snoc_castAdd, Fin.snoc_last, Fin.snoc_castSucc, SetGraphMapsAssignments]
  have castOne {k : Nat} (i : Fin k) : i.castAdd 1 = i.castSucc := rfl
  have castTwo {k : Nat} (i : Fin k) : i.castAdd 2 = i.castSucc.castSucc := rfl
  simp only [castOne, castTwo, Fin.snoc_castSucc, Fin.snoc_last]

def SetGraphPreservesSatisfaction (M : TransitiveClass.{u})
    (graph D E arityBook sourceTruth targetTruth : M.Element) : Prop :=
  ZFSet.IsFunc D.val E.val graph.val ∧
    ∀ code left right : M.Element,
      SetAssignmentAtCode M arityBook D code left → SetAssignmentAtCode M arityBook E code right →
      SetGraphMapsAssignments M graph left right →
        (ZFSet.pair code.val right.val ∈ targetTruth.val ↔ ZFSet.pair code.val left.val ∈ sourceTruth.val)

/-- One finite formula checks every encoded formula using two actual set
truth tables. The arity book and the two truth sets are explicit parameters. -/
def setGraphPreservesSatisfaction : RankPredicateFormula 0 6 :=
  let body : RankPredicateFormula 0 9 :=
    .imp (setValidAssignment 3 1 6 7) (.imp (setValidAssignment 3 2 6 8)
      (.imp (setAssignmentMapFormula 0 7 8)
        ((rankFormulaGraphApplies 5 6 8).iff (rankFormulaGraphApplies 4 6 7))))
  (rankFormulaFunction 0 1 2).and body.all.all.all

def setGraphPreservesSatisfactionFormula : membershipLanguage.Formula (Fin 6) :=
  rankPredicateToFormula setGraphPreservesSatisfaction

theorem setGraphPreservesSatisfaction_realize (stage : ModelStage.{u})
    (graph D E arityBook sourceTruth targetTruth : stage.model.Element) :
    stage.model.realize setGraphPreservesSatisfaction ![graph, D, E, arityBook, sourceTruth, targetTruth] ↔
      SetGraphPreservesSatisfaction stage.model graph D E arityBook sourceTruth targetTruth := by
  simp [setGraphPreservesSatisfaction, stage.model.realize_and, TransitiveClass.realize,
    stage.model.setFunctionAtom_realize, stage.model.setGraphAtom_realize,
    stage.model.pure_iff_realize, setValidAssignment_realize stage,
    setAssignmentMapFormula_realize, SetGraphPreservesSatisfaction]

namespace ModelStage

theorem setAssignment_maps_iff (stage : ModelStage.{u}) (graph D E : stage.model.Element)
    {n : Nat} (v : Fin n → SetDomain D.val) (w : Fin n → SetDomain E.val) :
    SetGraphMapsAssignments stage.model graph
      ⟨setAssignment v, stage.setAssignment_mem D v⟩ ⟨setAssignment w, stage.setAssignment_mem E w⟩ ↔
      ∀ i, ZFSet.pair (v i).val (w i).val ∈ graph.val := by
  constructor
  · intro h i
    exact h (stage.ordinal (i.val : Ordinal.{u})) (stage.model.setInclude D (v i))
      (stage.model.setInclude E (w i))
      ((setAssignment_applies_nat_iff _ _ _).mpr rfl) ((setAssignment_applies_nat_iff _ _ _).mpr rfl)
  · intro h i x y left right
    obtain ⟨k, hi, hx⟩ := (setAssignment_applies_iff _ _ _).mp left
    obtain ⟨l, hj, hy⟩ := (setAssignment_applies_iff _ _ _).mp right
    have same : k = l := Fin.ext (Nat.cast_injective (Ordinal.toZFSet_injective (hi.symm.trans hj)))
    rw [hx, hy, ← same]
    exact h k

/-- With the genuine truth sets, the one coded condition is equivalent to
the full elementary graph definition, including every finite formula. -/
theorem graphElementary_iff_setSatisfaction (stage : ModelStage.{u})
    (graph D E : stage.model.Element) :
    stage.model.GraphElementary graph D E ↔
      SetGraphPreservesSatisfaction stage.model graph D E (stage.syntaxBooks 0)
        (stage.setSatisfaction D) (stage.setSatisfaction E) := by
  constructor
  · intro elementary
    refine ⟨(stage.model.function_absolute _ _ _).mp elementary.1, ?_⟩
    intro code left right validLeft validRight mapped
    obtain ⟨n, phi, v, codeEq, leftEq⟩ := (stage.setAssignmentAtCode_iff D code left).mp validLeft
    obtain ⟨w, rightEq⟩ := (stage.setAssignmentAtCode_formula_iff E code right phi codeEq).mp validRight
    have leftSame : left = ⟨setAssignment v, stage.setAssignment_mem D v⟩ := Subtype.ext leftEq
    have rightSame : right = ⟨setAssignment w, stage.setAssignment_mem E w⟩ := Subtype.ext rightEq
    rw [leftSame, rightSame, stage.setAssignment_maps_iff] at mapped
    have values : w = elementary.toEmbedding ∘ v := by
      funext i
      exact ((elementary.applies_iff (v i) (w i)).mp
        ((stage.model.graphApplies_absolute _ _ _).mpr (mapped i))).symm
    rw [codeEq, leftEq, rightEq, stage.setSatisfaction_realize, stage.setSatisfaction_realize,
      SetDomain.realize_toFormula, SetDomain.realize_toFormula, values]
    exact elementary.toEmbedding.map_formula _ v
  · rintro ⟨function, preserves⟩
    refine ⟨(stage.model.function_absolute _ _ _).mpr function, ?_⟩
    intro n phi xs ys edges
    rw [stage.model.setFormula_realize, stage.model.setFormula_realize]
    let pure : RankPredicateFormula 0 n := rankPredicateAtom phi id
    have maps : SetGraphMapsAssignments stage.model graph
        ⟨setAssignment xs, stage.setAssignment_mem D xs⟩ ⟨setAssignment ys, stage.setAssignment_mem E ys⟩ :=
      (stage.setAssignment_maps_iff graph D E xs ys).mpr
        (fun i => (stage.model.graphApplies_absolute _ _ _).mp (edges i))
    have result := preserves (stage.ordinal (rankSyntaxCode ⟨n, pure⟩ : Ordinal.{u}))
      ⟨setAssignment xs, stage.setAssignment_mem D xs⟩ ⟨setAssignment ys, stage.setAssignment_mem E ys⟩
      (stage.setAssignmentAtCode_formula D pure xs) (stage.setAssignmentAtCode_formula E pure ys) maps
    change (ZFSet.pair (rankSyntaxCode ⟨n, pure⟩ : Ordinal.{u}).toZFSet (setAssignment ys) ∈
      (stage.setSatisfaction E).val ↔ ZFSet.pair (rankSyntaxCode ⟨n, pure⟩ : Ordinal.{u}).toZFSet
        (setAssignment xs) ∈ (stage.setSatisfaction D).val) at result
    simpa only [stage.setSatisfaction_realize, pure, SetDomain.realize_atom] using result

end ModelStage
end IBLP
