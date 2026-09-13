import IBLP.Model.Hierarchy
import IBLP.Model.Intersection
import IBLP.Rank.WeakEdges

namespace IBLP
open FullMarkedBLP
universe u

theorem ModelStage.hierarchy_zero (stage : ModelStage.{u}) : (stage.hierarchy 0).val = ∅ := by
  apply ZFSet.ext
  intro z
  simp only [stage.mem_hierarchy, not_lt_zero, and_false, ZFSet.notMem_empty]

theorem ModelStage.hierarchy_transitive (stage : ModelStage.{u}) (beta : Ordinal.{u}) :
    ZFSet.IsTransitive (stage.hierarchy beta).val := by
  intro x hx z hz
  obtain ⟨hm, hr⟩ := (stage.mem_hierarchy beta x).mp hx
  exact (stage.mem_hierarchy beta z).mpr
    ⟨stage.model.transitive hz hm, (ZFSet.rank_lt_of_mem hz).trans hr⟩

theorem ModelStage.hierarchy_mono (stage : ModelStage.{u}) {alpha beta : Ordinal.{u}}
    (h : alpha ≤ beta) : (stage.hierarchy alpha).val ⊆ (stage.hierarchy beta).val := by
  intro z hz
  obtain ⟨hm, hr⟩ := (stage.mem_hierarchy alpha z).mp hz
  exact (stage.mem_hierarchy beta z).mpr ⟨hm, hr.trans_le h⟩

theorem ModelStage.hierarchy_subset_iff (stage : ModelStage.{u}) (alpha beta : Ordinal.{u}) :
    (stage.hierarchy alpha).val ⊆ (stage.hierarchy beta).val ↔ alpha ≤ beta := by
  constructor
  · intro h
    simpa only [stage.hierarchy_rank] using ZFSet.rank_mono h
  · exact stage.hierarchy_mono

theorem ModelStage.hierarchy_mem_iff (stage : ModelStage.{u}) (alpha beta : Ordinal.{u}) :
    (stage.hierarchy alpha).val ∈ (stage.hierarchy beta).val ↔ alpha < beta := by
  rw [stage.mem_hierarchy_iff, stage.hierarchy_rank]

theorem ModelStage.ordinal_mem_hierarchy (stage : ModelStage.{u}) (alpha beta : Ordinal.{u}) :
    alpha.toZFSet ∈ (stage.hierarchy beta).val ↔ alpha < beta := by
  rw [stage.mem_hierarchy, Ordinal.rank_toZFSet]
  exact and_iff_right (stage.ordinalComplete alpha)

/-- 后继层恰为模型内部幂集，保留所有模型成员资格条件。 -/
theorem ModelStage.hierarchy_succ (stage : ModelStage.{u}) (beta : Ordinal.{u}) :
    stage.hierarchy (Order.succ beta) = stage.powerset (stage.hierarchy beta) := by
  apply stage.model.element_ext
  intro z
  rw [stage.mem_hierarchy_iff, stage.mem_powerset, Order.lt_succ_iff]
  constructor
  · intro hr w hw
    exact (stage.mem_hierarchy beta w).mpr
      ⟨stage.model.transitive hw z.property, (ZFSet.rank_lt_of_mem hw).trans_le hr⟩
  · intro subset
    apply ZFSet.rank_le_iff.mpr
    intro w hw
    exact ((stage.mem_hierarchy beta w).mp (subset hw)).2

theorem ModelStage.mem_hierarchy_limit (stage : ModelStage.{u}) {delta : Ordinal.{u}}
    (hd : Order.IsSuccLimit delta) (z : ZFSet.{u}) :
    z ∈ (stage.hierarchy delta).val ↔ ∃ beta < delta, z ∈ (stage.hierarchy beta).val := by
  constructor
  · intro hz
    obtain ⟨hm, hr⟩ := (stage.mem_hierarchy delta z).mp hz
    exact ⟨Order.succ z.rank, hd.succ_lt hr,
      (stage.mem_hierarchy _ z).mpr ⟨hm, Order.lt_succ _⟩⟩
  · rintro ⟨beta, below, hz⟩
    exact stage.hierarchy_mono below.le hz

/-- 内部截断先由模型内部交集构造；随后证明与实际秩截断相同。 -/
noncomputable def ModelStage.cut (stage : ModelStage.{u}) (beta : Ordinal.{u})
    (z : stage.model.Element) : stage.model.Element := stage.intersection z (stage.hierarchy beta)

theorem ModelStage.cut_val (stage : ModelStage.{u}) (beta : Ordinal.{u}) (z : stage.model.Element) :
    (stage.cut beta z).val = z.val ∩ ZFSet.vonNeumann beta := by
  apply ZFSet.ext
  intro w
  rw [ModelStage.cut, stage.intersection_val, ZFSet.mem_inter, stage.mem_hierarchy,
    ZFSet.mem_inter, ZFSet.mem_vonNeumann]
  constructor
  · exact fun h => ⟨h.1, h.2.2⟩
  · exact fun h => ⟨h.1, stage.model.transitive h.1 z.property, h.2⟩

/-- 截断封闭从已构造的内部累计层推出，不再是 stage 的额外前提。 -/
noncomputable def ModelStage.rankClosed (stage : ModelStage.{u}) : RankClosedClass.{u} where
  toTransitiveClass := stage.model
  cut_mem := by
    intro z hz beta
    have inside := (stage.cut beta ⟨z, hz⟩).property
    rwa [stage.cut_val] at inside

noncomputable def ModelStage.cutSpace (stage : ModelStage.{u}) : CutSpace.{u} stage.model.Element :=
  stage.rankClosed.cutSpace

theorem ModelStage.cutSpace_cut (stage : ModelStage.{u}) (beta : Ordinal.{u}) (z : stage.model.Element) :
    stage.cutSpace.cut beta z = stage.cut beta z :=
  Subtype.ext (stage.cut_val beta z).symm

/-- 既有弱相等读取序数边的定理可直接用于这个真实内部截断空间。 -/
noncomputable def ModelStage.ordinalView (stage : ModelStage.{u}) : OrdinalView stage.cutSpace where
  elem := stage.ordinal
  rank_elem := Ordinal.rank_toZFSet
  mem_elem := fun _ _ => Ordinal.toZFSet_mem_toZFSet_iff

end IBLP
