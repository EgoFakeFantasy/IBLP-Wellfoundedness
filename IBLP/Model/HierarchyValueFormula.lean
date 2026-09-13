import IBLP.Model.UniformAtoms
import IBLP.Model.Hierarchy

namespace IBLP
open FullMarkedBLP FirstOrder Language
universe u

/-- Parameters are the ordinal index and the hierarchy value; the finite
witnesses are a longer ordinal domain, its range and its recursion graph. -/
def hierarchyValueBody : RankPredicateFormula 0 5 :=
  (rankPredicateAtom rankOrdinalFormula ![0]).and
    ((rankPredicateAtom rankOrdinalFormula ![2]).and
      ((RankPredicateFormula.member 0 2).and
        ((rankPredicateAtom rankFunctionFormula ![4, 2, 3]).and
          ((rankPredicateAtom rankHierarchyRecFormula ![4]).and
            (rankPredicateAtom rankGraphAppliesFormula ![4, 0, 1])))))

def hierarchyValueMatrix : RankPredicateFormula 0 2 := hierarchyValueBody.ex.ex.ex

def HierarchyValueWitness (stage : ModelStage.{u}) (alpha value : stage.model.Element) : Prop :=
  ∃ domain range graph : stage.model.Element,
    ZFSet.IsOrdinal alpha.val ∧ ZFSet.IsOrdinal domain.val ∧ alpha.val ∈ domain.val ∧
      stage.model.IsFunction graph domain range ∧ stage.model.HierarchyRec graph ∧
      stage.model.GraphApplies graph alpha value

theorem hierarchyValueBody_realize (stage : ModelStage.{u}) (values : Fin 5 → stage.model.Element) :
    stage.model.realize hierarchyValueBody values ↔
      ZFSet.IsOrdinal (values 0).val ∧ ZFSet.IsOrdinal (values 2).val ∧ (values 0).val ∈ (values 2).val ∧
        stage.model.IsFunction (values 4) (values 2) (values 3) ∧ stage.model.HierarchyRec (values 4) ∧
        stage.model.GraphApplies (values 4) (values 0) (values 1) := by
  simp only [hierarchyValueBody, stage.model.realize_and, stage.model.realize_atom, TransitiveClass.realize]
  have ordinal0 : values ∘ ![(0 : Fin 5)] = ![values 0] := by funext i; fin_cases i; rfl
  have ordinal2 : values ∘ ![(2 : Fin 5)] = ![values 2] := by funext i; fin_cases i; rfl
  have function : values ∘ ![(4 : Fin 5), 2, 3] = ![values 4, values 2, values 3] := by
    funext i; fin_cases i <;> rfl
  have recursion : values ∘ ![(4 : Fin 5)] = ![values 4] := by funext i; fin_cases i; rfl
  have edge : values ∘ ![(4 : Fin 5), 0, 1] = ![values 4, values 0, values 1] := by
    funext i; fin_cases i <;> rfl
  rw [ordinal0, ordinal2, function, recursion, edge, stage.model.ordinalFormula_realize,
    stage.model.ordinalFormula_realize, stage.model.functionFormula_realize,
    stage.model.hierarchyRecFormula_realize, stage.model.graphAppliesFormula_realize]

theorem hierarchyValueMatrix_realize (stage : ModelStage.{u}) (alpha value : stage.model.Element) :
    stage.model.realize hierarchyValueMatrix ![alpha, value] ↔ HierarchyValueWitness stage alpha value := by
  simp only [hierarchyValueMatrix, stage.model.realize_ex, hierarchyValueBody_realize, HierarchyValueWitness]
  rfl

/-- Exact decoding of the finite hierarchy witness. Its index and value
are precisely the actual ordinal and the actual model-relative rank set. -/
theorem hierarchyValueWitness_iff (stage : ModelStage.{u}) (alpha value : stage.model.Element) :
    HierarchyValueWitness stage alpha value ↔
      ∃ beta : Ordinal.{u}, alpha = stage.ordinal beta ∧ value = stage.hierarchy beta := by
  constructor
  · rintro ⟨domain, range, graph, ordinal, domainOrdinal, member, function, recursion, edge⟩
    have representation : alpha = stage.ordinal alpha.val.rank := Subtype.ext ordinal.toZFSet_rank_eq.symm
    refine ⟨alpha.val.rank, representation, ?_⟩
    apply Subtype.ext
    apply ZFSet.ext
    intro z
    exact (stage.model.hierarchyRec_mem_iff function domainOrdinal recursion alpha.val.rank alpha value
      (congrArg Subtype.val representation) member edge z).trans (stage.mem_hierarchy alpha.val.rank z).symm
  · rintro ⟨beta, rfl, rfl⟩
    obtain ⟨range, graph, function, recursion⟩ :=
      stage.hierarchy_graph_exists (stage.ordinal (Order.succ beta)) (ZFSet.isOrdinal_toZFSet _)
    have member : (stage.ordinal beta).val ∈ (stage.ordinal (Order.succ beta)).val :=
      Ordinal.toZFSet_mem_toZFSet_iff.mpr (Order.lt_succ beta)
    obtain ⟨value, _, edge, _⟩ := function.2 (stage.ordinal beta) member
    have same : value = stage.hierarchy beta := by
      apply Subtype.ext
      apply ZFSet.ext
      intro z
      exact (stage.model.hierarchyRec_mem_iff function (ZFSet.isOrdinal_toZFSet _) recursion beta
        (stage.ordinal beta) value rfl member edge z).trans (stage.mem_hierarchy beta z).symm
    rw [same] at edge
    exact ⟨stage.ordinal (Order.succ beta), range, graph, ZFSet.isOrdinal_toZFSet _,
      ZFSet.isOrdinal_toZFSet _, member, function, recursion, edge⟩

theorem UniformDefinable.hierarchy_value : UniformDefinable
    (fun (stage : ModelStage.{u}) (values : Fin 2 → _) =>
      ∃ beta : Ordinal.{u}, values 0 = stage.ordinal beta ∧ values 1 = stage.hierarchy beta) :=
  (UniformDefinable.of_matrix hierarchyValueMatrix).congr (fun stage values => by
    have tuple : values = ![values 0, values 1] := by funext i; fin_cases i <;> rfl
    conv_lhs => rw [tuple]
    exact (hierarchyValueMatrix_realize stage (values 0) (values 1)).trans
      (hierarchyValueWitness_iff stage (values 0) (values 1)))

end IBLP
