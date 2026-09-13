import IBLP.Model.Hierarchy
import FullMarkedBLP.RankGraphClosure

namespace IBLP
open FullMarkedBLP
universe u

/-- A hierarchy sequence selected from the actual internal graph-existence
theorem. Its initial witness range is subsequently tightened to `V_upper^M`. -/
noncomputable def ModelStage.hierarchyGraph (stage : ModelStage.{u}) (upper : Ordinal.{u}) :
    stage.model.Element :=
  (stage.hierarchy_graph_exists (stage.ordinal upper) (ZFSet.isOrdinal_toZFSet upper)).choose_spec.choose

theorem ModelStage.hierarchyGraph_spec (stage : ModelStage.{u}) (upper : Ordinal.{u}) :
    ∃ range : stage.model.Element,
      stage.model.IsFunction (stage.hierarchyGraph upper) (stage.ordinal upper) range ∧
      stage.model.HierarchyRec (stage.hierarchyGraph upper) := by
  exact ⟨(stage.hierarchy_graph_exists (stage.ordinal upper) (ZFSet.isOrdinal_toZFSet upper)).choose,
    (stage.hierarchy_graph_exists (stage.ordinal upper)
      (ZFSet.isOrdinal_toZFSet upper)).choose_spec.choose_spec⟩

theorem ModelStage.hierarchyGraph_recursion (stage : ModelStage.{u}) (upper : Ordinal.{u}) :
    stage.model.HierarchyRec (stage.hierarchyGraph upper) := (stage.hierarchyGraph_spec upper).choose_spec.2

theorem ModelStage.hierarchyGraph_applies_iff (stage : ModelStage.{u}) (upper : Ordinal.{u})
    (i value : stage.model.Element) :
    stage.model.GraphApplies (stage.hierarchyGraph upper) i value ↔
      i.val ∈ upper.toZFSet ∧ value = stage.hierarchy i.val.rank := by
  obtain ⟨range, function, recursion⟩ := stage.hierarchyGraph_spec upper
  have image (i value : stage.model.Element)
      (edge : stage.model.GraphApplies (stage.hierarchyGraph upper) i value) :
      i.val ∈ upper.toZFSet ∧ value = stage.hierarchy i.val.rank := by
    have actual := (stage.model.function_absolute _ _ _).mp function
    have edge' := (stage.model.graphApplies_absolute _ _ _).mp edge
    have member : i.val ∈ upper.toZFSet := (ZFSet.pair_mem_prod.mp (actual.1 edge')).1
    obtain ⟨beta, _, representation⟩ := Ordinal.mem_toZFSet_iff.mp member
    have levelRepresentation : i.val = i.val.rank.toZFSet := by
      rw [← representation, Ordinal.rank_toZFSet]
    refine ⟨member, ?_⟩
    apply Subtype.ext
    apply ZFSet.ext
    intro z
    rw [stage.mem_hierarchy]
    exact stage.model.hierarchyRec_mem_iff function (ZFSet.isOrdinal_toZFSet _) recursion
      i.val.rank i value levelRepresentation member edge z
  constructor
  · exact image i value
  · rintro ⟨member, valueEq⟩
    obtain ⟨b, _, edge, _⟩ := function.2 i member
    have bEq := (image i b edge).2
    have same : b = value := bEq.trans valueEq.symm
    simpa only [same] using edge

theorem ModelStage.hierarchyGraph_isFunction (stage : ModelStage.{u}) (upper : Ordinal.{u}) :
    stage.model.IsFunction (stage.hierarchyGraph upper) (stage.ordinal upper) (stage.hierarchy upper) := by
  obtain ⟨range, function, _⟩ := stage.hierarchyGraph_spec upper
  have rangeBound (i value : stage.model.Element)
      (edge : stage.model.GraphApplies (stage.hierarchyGraph upper) i value) :
      value.val ∈ (stage.hierarchy upper).val := by
    obtain ⟨member, valueEq⟩ := (stage.hierarchyGraph_applies_iff upper i value).mp edge
    rw [stage.mem_hierarchy_iff, valueEq, stage.hierarchy_rank]
    simpa only [Ordinal.rank_toZFSet] using ZFSet.rank_lt_of_mem member
  constructor
  · intro p hp
    obtain ⟨a, b, ha, _, pair⟩ := function.1 p hp
    have edge : stage.model.GraphApplies (stage.hierarchyGraph upper) a b := ⟨p, hp, pair⟩
    exact ⟨a, b, ha, rangeBound a b edge, pair⟩
  · intro a ha
    obtain ⟨b, _, edge, unique⟩ := function.2 a ha
    exact ⟨b, rangeBound a b edge, edge, unique⟩

/-- The selected graph is a genuine set function into the model's upper level. -/
theorem ModelStage.hierarchyGraph_function (stage : ModelStage.{u}) (upper : Ordinal.{u}) :
    ZFSet.IsFunc upper.toZFSet (stage.hierarchy upper).val (stage.hierarchyGraph upper).val :=
  (stage.model.function_absolute _ _ _).mp (stage.hierarchyGraph_isFunction upper)

/-- The entire internal recursion graph belongs to every larger limit rank. -/
theorem ModelStage.hierarchyGraph_rank_lt (stage : ModelStage.{u})
    {lambda upper : Ordinal.{u}} (limit : Order.IsSuccLimit lambda) (below : upper < lambda) :
    (stage.hierarchyGraph upper).val.rank < lambda := by
  apply rank_function_lt_of_limit limit _ _ (stage.hierarchyGraph_function upper)
  · simpa only [Ordinal.rank_toZFSet] using below
  · simpa only [stage.hierarchy_rank] using below

end IBLP
