import IBLP.Model.HierarchyRec
import IBLP.Model.UniverseHierarchy

namespace IBLP
open FullMarkedBLP FirstOrder Language
universe u

/-- Variables are domain, range, graph. Every quantifier in the atoms is
interpreted in the current model. -/
def hierarchyGraphBody : RankPredicateFormula 0 3 :=
  (rankPredicateAtom rankFunctionFormula ![2, 0, 1]).and
    (rankPredicateAtom rankHierarchyRecFormula ![2])

def hierarchyGraphExistsFormula : RankPredicateFormula 0 1 :=
  .imp (rankPredicateAtom rankOrdinalFormula ![0]) hierarchyGraphBody.ex.ex

theorem TransitiveClass.hierarchyGraphBody_realize (M : TransitiveClass.{u})
    (values : Fin 3 → M.Element) :
    M.realize hierarchyGraphBody values ↔
      M.IsFunction (values 2) (values 0) (values 1) ∧ M.HierarchyRec (values 2) := by
  rw [hierarchyGraphBody, M.realize_and, M.realize_atom, M.realize_atom]
  have tupleFunction : values ∘ ![2, 0, 1] = ![values 2, values 0, values 1] := by
    funext i; fin_cases i <;> rfl
  have tupleRec : values ∘ ![2] = ![values 2] := by funext i; fin_cases i; rfl
  rw [tupleFunction, tupleRec, M.functionFormula_realize, M.hierarchyRecFormula_realize]

theorem TransitiveClass.hierarchyGraphExistsFormula_realize (M : TransitiveClass.{u})
    (values : Fin 1 → M.Element) :
    M.realize hierarchyGraphExistsFormula values ↔
      ZFSet.IsOrdinal (values 0).val → ∃ range graph : M.Element,
        M.IsFunction graph (values 0) range ∧ M.HierarchyRec graph := by
  change (M.realize (rankPredicateAtom rankOrdinalFormula ![0]) values →
    M.realize hierarchyGraphBody.ex.ex values) ↔ _
  rw [M.realize_atom]
  have tuple : values ∘ ![0] = ![values 0] := by funext i; fin_cases i; rfl
  rw [tuple, M.ordinalFormula_realize]
  apply imp_congr Iff.rfl
  simp only [M.realize_ex]
  apply exists_congr
  intro range
  apply exists_congr
  intro graph
  rw [M.hierarchyGraphBody_realize]
  rfl

theorem universeClass_hierarchyRec (upper : Ordinal.{u}) :
    universeClass.toTransitiveClass.HierarchyRec
      ⟨universeHierarchyGraph upper, Set.mem_univ _⟩ := by
  intro i value edge z
  have edge' := (universeClass.toTransitiveClass.graphApplies_absolute _ _ _).mp edge
  rw [universeHierarchyGraph_recursion upper i.val value.val edge' z.val]
  constructor
  · rintro ⟨a, b, smaller, applies, subset⟩
    refine ⟨⟨a, Set.mem_univ _⟩, ⟨b, Set.mem_univ _⟩, smaller, ?_, ?_⟩
    · exact (universeClass.toTransitiveClass.graphApplies_absolute _ _ _).mpr applies
    · exact fun _ hw => subset hw
  · rintro ⟨a, b, smaller, applies, subset⟩
    refine ⟨a.val, b.val, smaller, ?_, ?_⟩
    · exact (universeClass.toTransitiveClass.graphApplies_absolute _ _ _).mp applies
    · intro w hw
      exact subset ⟨w, Set.mem_univ _⟩ hw

/-- Graph existence is transferred by one concrete finite formula, whose truth
in the initial universe is witnessed by the constructed hierarchy graph. -/
theorem ModelStage.hierarchy_graph_exists (stage : ModelStage.{u})
    (domain : stage.model.Element) (ordinal : ZFSet.IsOrdinal domain.val) :
    ∃ range graph : stage.model.Element,
      stage.model.IsFunction graph domain range ∧ stage.model.HierarchyRec graph := by
  have initial : ∀ values, universeClass.{u}.toTransitiveClass.realize
      hierarchyGraphExistsFormula values := by
    intro values
    apply (universeClass.toTransitiveClass.hierarchyGraphExistsFormula_realize values).mpr
    intro hOrdinal
    let upper := (values 0).val.rank
    refine ⟨⟨ZFSet.vonNeumann upper, Set.mem_univ _⟩,
      ⟨universeHierarchyGraph upper, Set.mem_univ _⟩, ?_, universeClass_hierarchyRec upper⟩
    apply (universeClass.toTransitiveClass.function_absolute _ _ _).mpr
    have representation : (values 0).val = upper.toZFSet := hOrdinal.toZFSet_rank_eq.symm
    change ZFSet.IsFunc (values 0).val (ZFSet.vonNeumann upper) (universeHierarchyGraph upper)
    rw [representation]
    exact universeHierarchyGraph_function upper
  have transferred := stage.transfer_schema hierarchyGraphExistsFormula initial ![domain]
  exact (stage.model.hierarchyGraphExistsFormula_realize ![domain]).mp transferred ordinal

end IBLP
