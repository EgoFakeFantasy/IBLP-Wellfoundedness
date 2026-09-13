import IBLP.Model.GraphEqualizer
import IBLP.Model.CountableImage

namespace IBLP
open FullMarkedBLP
universe u

theorem graph_value_mem_doubleUnion {graph index value : ZFSet.{u}}
    (edge : ZFSet.pair index value ∈ graph) : value ∈ ZFSet.sUnion (ZFSet.sUnion graph) := by
  apply ZFSet.mem_sUnion.mpr
  refine ⟨{index, value}, ?_, by simp⟩
  apply ZFSet.mem_sUnion.mpr
  exact ⟨ZFSet.pair index value, edge, by simp [ZFSet.pair]⟩

/-- Reading an arbitrary graph returns the union of all values at the index.
For a single-valued graph this is its unique value; arbitrary inputs remain total. -/
def graphReadRelation : RankPredicateFormula 0 3 :=
  .all ((RankPredicateFormula.member 3 2).iff
    (((rankPredicateAtom rankGraphAppliesFormula ![1, 0, 4]).and (.member 3 4)).ex))

theorem graphReadRelation_realize (M : TransitiveClass.{u}) (index graph result : M.Element) :
    M.realize graphReadRelation ![index, graph, result] ↔
      ∀ z : M.Element, z.val ∈ result.val ↔
        ∃ y : M.Element, ZFSet.pair index.val y.val ∈ graph.val ∧ z.val ∈ y.val := by
  simp [graphReadRelation, RankPredicateFormula.iff, M.realize_and, M.realize_ex,
    M.graphFormulaAtom_realize, TransitiveClass.realize, iff_def]

def graphReadValue (index graph result : ZFSet.{u}) : Prop :=
  ∀ z, z ∈ result ↔ ∃ y, ZFSet.pair index y ∈ graph ∧ z ∈ y

theorem graphReadRelation_absolute (M : TransitiveClass.{u}) (index graph result : M.Element) :
    M.realize graphReadRelation ![index, graph, result] ↔ graphReadValue index.val graph.val result.val := by
  rw [graphReadRelation_realize]
  constructor
  · intro h z
    constructor
    · intro hz
      obtain ⟨y, edge, member⟩ := (h (M.member result z hz)).mp hz
      exact ⟨y.val, edge, member⟩
    · rintro ⟨y, edge, member⟩
      let ym : M.Element := ⟨y, (M.pair_components (M.transitive edge graph.property)).2⟩
      exact (h (M.member ym z member)).mpr ⟨ym, edge, member⟩
  · intro h z
    rw [h z.val]
    constructor
    · rintro ⟨y, edge, member⟩
      exact ⟨⟨y, (M.pair_components (M.transitive edge graph.property)).2⟩, edge, member⟩
    · rintro ⟨y, edge, member⟩
      exact ⟨y.val, edge, member⟩

namespace ModelStage

noncomputable def graphRead (stage : ModelStage.{u}) (index graph : stage.model.Element) : stage.model.Element :=
  stage.union (stage.separation (rankPredicateAtom rankGraphAppliesFormula ![1, 0, 2]) ![index, graph]
    (stage.union (stage.union graph)))

theorem mem_graphRead (stage : ModelStage.{u}) (index graph : stage.model.Element) (z : ZFSet.{u}) :
    z ∈ (stage.graphRead index graph).val ↔ ∃ y, ZFSet.pair index.val y ∈ graph.val ∧ z ∈ y := by
  rw [graphRead, stage.union_val, ZFSet.mem_sUnion]
  constructor
  · rintro ⟨y, hy, hz⟩
    let ym := stage.model.member (stage.separation _ _ _) y hy
    have spec := (stage.mem_separation _ _ _ ym).mp hy
    exact ⟨y, (stage.model.graphFormulaAtom_realize _ _ _ _).mp spec.2, hz⟩
  · rintro ⟨y, edge, hz⟩
    let ym : stage.model.Element := ⟨y, (stage.model.pair_components (stage.model.transitive edge graph.property)).2⟩
    refine ⟨y, (stage.mem_separation _ _ _ ym).mpr ⟨?_, ?_⟩, hz⟩
    · rw [stage.union_val, stage.union_val]
      exact graph_value_mem_doubleUnion edge
    · exact (stage.model.graphFormulaAtom_realize _ _ _ _).mpr edge

theorem graphRead_satisfies (stage : ModelStage.{u}) (index graph : stage.model.Element) :
    stage.model.realize graphReadRelation ![index, graph, stage.graphRead index graph] := by
  apply (graphReadRelation_realize _ _ _ _).mpr
  intro z
  rw [stage.mem_graphRead]
  constructor
  · rintro ⟨y, edge, hz⟩
    exact ⟨⟨y, (stage.model.pair_components (stage.model.transitive edge graph.property)).2⟩, edge, hz⟩
  · rintro ⟨y, edge, hz⟩
    exact ⟨y.val, edge, hz⟩

theorem graphRead_unique (stage : ModelStage.{u}) (index graph result : stage.model.Element)
    (h : stage.model.realize graphReadRelation ![index, graph, result]) : result = stage.graphRead index graph := by
  apply stage.model.element_ext
  intro z
  rw [(graphReadRelation_realize _ _ _ _).mp h z,
    (graphReadRelation_realize _ _ _ _).mp (stage.graphRead_satisfies index graph) z]

theorem graphRead_rank_le (stage : ModelStage.{u}) (index graph : stage.model.Element) :
    (stage.graphRead index graph).val.rank ≤ graph.val.rank := by
  apply ZFSet.rank_le_iff.mpr
  intro z hz
  obtain ⟨y, edge, member⟩ := (stage.mem_graphRead index graph z).mp hz
  have yrank := ZFSet.rank_lt_of_mem (graph_value_mem_doubleUnion edge)
  exact (ZFSet.rank_lt_of_mem member).trans
    (yrank.trans_le ((ZFSet.rank_sUnion_le _).trans (ZFSet.rank_sUnion_le _)))

theorem graphRead_of_unique (stage : ModelStage.{u}) (index graph value : stage.model.Element)
    (edge : ZFSet.pair index.val value.val ∈ graph.val)
    (unique : ∀ y, ZFSet.pair index.val y ∈ graph.val → y = value.val) :
    stage.graphRead index graph = value := by
  apply Subtype.ext
  apply ZFSet.ext
  intro z
  rw [stage.mem_graphRead]
  exact ⟨fun ⟨y, hy, hz⟩ => unique y hy ▸ hz, fun hz => ⟨value.val, edge, hz⟩⟩

theorem graphRead_countableGraph (stage : ModelStage.{u}) (f : Nat → stage.model.Element) (n : Nat) :
    stage.graphRead (stage.ordinal (n : Ordinal.{u})) (stage.countableGraph f) = f n := by
  refine stage.graphRead_of_unique _ _ _ ?_ ?_
  · exact ZFSet.mem_range.mpr ⟨n, rfl⟩
  · intro y hy
    obtain ⟨m, hm⟩ := ZFSet.mem_range.mp hy
    obtain ⟨indices, values⟩ := ZFSet.pair_inj.mp hm
    have same : m = n := Nat.cast_injective (Ordinal.toZFSet_injective indices)
    simpa only [same] using values.symm

end ModelStage
end IBLP
