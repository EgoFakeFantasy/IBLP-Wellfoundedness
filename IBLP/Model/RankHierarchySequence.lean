import IBLP.Model.BoundedMap
import IBLP.Model.HierarchySequence

namespace IBLP
open FullMarkedBLP
universe u

namespace ModelStage

/-- Place an actually constructed small hierarchy graph in a larger internal
rank cut. The larger cut may be a successor rank. -/
noncomputable def hierarchyGraphIn (stage : ModelStage.{u}) {alpha lambda : Ordinal.{u}}
    (ha : Order.IsSuccLimit alpha) (h : alpha ≤ lambda) (upper : OrdinalDomain alpha) :
    stage.model.RankElement lambda :=
  ⟨(stage.hierarchyGraph upper.val).val, (stage.hierarchyGraph upper.val).property,
    (stage.hierarchyGraph_rank_lt ha upper.property).trans_le h⟩

theorem hierarchyGraphIn_function (stage : ModelStage.{u}) {alpha lambda : Ordinal.{u}}
    (ha : Order.IsSuccLimit alpha) (h : alpha ≤ lambda) (upper : OrdinalDomain alpha) :
    (stage.model.rankPart lambda).IsFunction (stage.hierarchyGraphIn ha h upper)
      (stage.rankOrdinal (includeOrdinal h upper)) (stage.rankHierarchy (includeOrdinal h upper)) :=
  ((stage.model.rankPart lambda).function_absolute _ _ _).mpr (stage.hierarchyGraph_function upper.val)

theorem hierarchyGraphIn_applies_iff (stage : ModelStage.{u}) {alpha lambda : Ordinal.{u}}
    (ha : Order.IsSuccLimit alpha) (h : alpha ≤ lambda) (upper : OrdinalDomain alpha)
    (i value : stage.model.RankElement lambda) :
    (stage.model.rankPart lambda).GraphApplies (stage.hierarchyGraphIn ha h upper) i value ↔
      i.val ∈ upper.val.toZFSet ∧ value.val = (stage.hierarchy i.val.rank).val := by
  rw [(stage.model.rankPart lambda).graphApplies_absolute]
  have semantic := stage.hierarchyGraph_applies_iff upper.val
    (stage.rankInclude lambda i) (stage.rankInclude lambda value)
  rw [stage.model.graphApplies_absolute] at semantic
  constructor
  · intro edge
    obtain ⟨member, image⟩ := semantic.mp edge
    exact ⟨member, congrArg Subtype.val image⟩
  · rintro ⟨member, image⟩
    exact semantic.mpr ⟨member, Subtype.ext image⟩

theorem hierarchyGraphIn_at (stage : ModelStage.{u}) {alpha lambda : Ordinal.{u}}
    (ha : Order.IsSuccLimit alpha) (h : alpha ≤ lambda) {upper beta : OrdinalDomain alpha}
    (below : beta < upper) :
    (stage.model.rankPart lambda).GraphApplies (stage.hierarchyGraphIn ha h upper)
      (stage.rankOrdinal (includeOrdinal h beta)) (stage.rankHierarchy (includeOrdinal h beta)) := by
  apply (stage.hierarchyGraphIn_applies_iff ha h upper _ _).mpr
  exact ⟨Ordinal.toZFSet_mem_toZFSet_iff.mpr below,
    by simp only [stage.rankOrdinal_val, stage.rankHierarchy_val, Ordinal.rank_toZFSet]⟩

/-- Restricting the quantifiers to the larger rank cut retains precisely the
internal recursion, because every needed lower layer and witness is present. -/
theorem hierarchyGraphIn_recursion (stage : ModelStage.{u}) {alpha lambda : Ordinal.{u}}
    (ha : Order.IsSuccLimit alpha) (h : alpha ≤ lambda) (upper : OrdinalDomain alpha) :
    (stage.model.rankPart lambda).HierarchyRec (stage.hierarchyGraphIn ha h upper) := by
  intro i value applies z
  obtain ⟨member, image⟩ := (stage.hierarchyGraphIn_applies_iff ha h upper i value).mp applies
  obtain ⟨beta, below, representation⟩ := Ordinal.mem_toZFSet_iff.mp member
  let level : OrdinalDomain alpha := ⟨beta, below.trans upper.property⟩
  have same : stage.rankOrdinal (includeOrdinal h level) = i := Subtype.ext representation
  subst i
  simp only [stage.rankOrdinal_val, includeOrdinal, Ordinal.rank_toZFSet] at image
  rw [image]
  constructor
  · intro hz
    have rankBound := ((stage.mem_hierarchy beta z.val).mp hz).2
    obtain ⟨gamma, less, subset⟩ :=
      ZFSet.mem_vonNeumann'.mp (ZFSet.mem_vonNeumann.mpr rankBound)
    let lower : OrdinalDomain alpha := ⟨gamma, less.trans level.property⟩
    refine ⟨stage.rankOrdinal (includeOrdinal h lower), stage.rankHierarchy (includeOrdinal h lower),
      Ordinal.toZFSet_mem_toZFSet_iff.mpr less, stage.hierarchyGraphIn_at ha h (less.trans below), ?_⟩
    intro w hw
    exact (stage.mem_hierarchy gamma w.val).mpr ⟨w.property.1, ZFSet.mem_vonNeumann.mp (subset hw)⟩
  · rintro ⟨a, b, smaller, edge, subset⟩
    have less : a.val.rank < beta := by
      simpa only [stage.rankOrdinal_val, includeOrdinal, Ordinal.rank_toZFSet] using ZFSet.rank_lt_of_mem smaller
    have valueEq := ((stage.hierarchyGraphIn_applies_iff ha h upper a b).mp edge).2
    apply (stage.mem_hierarchy beta z.val).mpr
    refine ⟨z.property.1, ZFSet.mem_vonNeumann.mp ?_⟩
    apply ZFSet.mem_vonNeumann'.mpr
    refine ⟨a.val.rank, less, ?_⟩
    intro w hw
    have included := subset ((stage.model.rankPart lambda).member z w hw) hw
    rw [valueEq] at included
    exact ZFSet.mem_vonNeumann.mpr ((stage.mem_hierarchy a.val.rank w).mp included).2

end ModelStage
end IBLP
