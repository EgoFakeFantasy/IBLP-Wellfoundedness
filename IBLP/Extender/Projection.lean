import IBLP.Extender.DerivedSystem
import IBLP.Model.Preimage
import FullMarkedBLP.ZFFunctionEquiv

namespace IBLP.Extender
open FullMarkedBLP
universe u

namespace Derivation
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}

/-- An actual internal total index map. Its graph belongs to the source
successor rank, so the given bounded elementary map can act on it. -/
structure IndexMap (stage : ModelStage.{u}) (alpha : Ordinal.{u}) where
  graph : Test stage alpha
  function : ZFSet.IsFunc (stage.hierarchy alpha).val (stage.hierarchy alpha).val graph.val

theorem map_index_function (D : Derivation stage alpha beta) (p : IndexMap stage alpha) :
    ZFSet.IsFunc (stage.hierarchy beta).val (stage.hierarchy beta).val (D.map p.graph).val := by
  have h := (D.map.function_iff p.graph top top).mpr p.function
  change ZFSet.IsFunc (D.map (stage.rankHierarchy (endpoint alpha))).val
    (D.map (stage.rankHierarchy (endpoint alpha))).val (D.map p.graph).val at h
  rw [stage.boundedMap_top] at h
  exact h

noncomputable def project (D : Derivation stage alpha beta) (p : IndexMap stage alpha)
    (seed : Seed stage beta) : Seed stage beta :=
  let y := zfGraphFunction (D.map_index_function p)
    ⟨seed.val, (stage.mem_hierarchy beta seed.val).mpr seed.property⟩
  ⟨y.val, (stage.mem_hierarchy beta y.val).mp y.property⟩

theorem project_edge (D : Derivation stage alpha beta) (p : IndexMap stage alpha)
    (seed : Seed stage beta) : ZFSet.pair seed.val (D.project p seed).val ∈ (D.map p.graph).val :=
  zfGraphFunction_edge (D.map_index_function p) _

theorem project_unique (D : Derivation stage alpha beta) (p : IndexMap stage alpha)
    (seed : Seed stage beta) (y : ZFSet.{u}) (edge : ZFSet.pair seed.val y ∈ (D.map p.graph).val) :
    y = (D.project p seed).val :=
  ((D.map_index_function p).2 seed.val ((stage.mem_hierarchy beta seed.val).mpr seed.property)).unique
    edge (D.project_edge p seed)

noncomputable def preimage (p : IndexMap stage alpha) (x : Test stage alpha) : Test stage alpha :=
  let y := stage.graphPreimage (stage.hierarchy alpha) (stage.rankInclude _ p.graph) (stage.rankInclude _ x)
  ⟨y.val, y.property, by
    apply Order.lt_succ_of_le
    apply (ZFSet.rank_mono (show y.val ⊆ (stage.hierarchy alpha).val from ?_)).trans_eq
      (stage.hierarchy_rank alpha)
    intro z hz
    rw [stage.graphPreimage_val, ZFSet.mem_sep] at hz
    exact hz.1⟩

theorem preimage_val (p : IndexMap stage alpha) (x : Test stage alpha) :
    (preimage p x).val = ZFSet.sep
      (fun z => ∃ y, ZFSet.pair z y ∈ p.graph.val ∧ y ∈ x.val) (stage.hierarchy alpha).val :=
  stage.graphPreimage_val _ _ _

theorem map_preimage_val (D : Derivation stage alpha beta) (p : IndexMap stage alpha)
    (x : Test stage alpha) :
    (D.map (preimage p x)).val = ZFSet.sep
      (fun z => ∃ y, ZFSet.pair z y ∈ (D.map p.graph).val ∧ y ∈ (D.map x).val)
      (stage.hierarchy beta).val := by
  have h := (D.map.preimage_iff top p.graph x (preimage p x)).mpr (preimage_val p x)
  change (D.map (preimage p x)).val = ZFSet.sep _
    (D.map (stage.rankHierarchy (endpoint alpha))).val at h
  rw [stage.boundedMap_top] at h
  exact h

/-- Pullback of a test along a genuine source graph agrees exactly with
evaluation at the corresponding projected target seed. -/
theorem large_preimage_iff (D : Derivation stage alpha beta) (p : IndexMap stage alpha)
    (seed : Seed stage beta) (x : Test stage alpha) :
    D.Large seed (preimage p x) ↔ D.Large (D.project p seed) x := by
  change seed.val ∈ (D.map (preimage p x)).val ↔ (D.project p seed).val ∈ (D.map x).val
  rw [D.map_preimage_val, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, y, edge, hy⟩
    rwa [D.project_unique p seed y edge] at hy
  · intro h
    exact ⟨(stage.mem_hierarchy beta seed.val).mpr seed.property,
      (D.project p seed).val, D.project_edge p seed, h⟩

theorem measure_preimage_iff (D : Derivation stage alpha beta) (p : IndexMap stage alpha)
    (seed : Seed stage beta) (x : Test stage alpha) :
    (preimage p x).val ∈ (D.measure seed).val ↔ x.val ∈ (D.measure (D.project p seed)).val := by
  simp only [D.mem_measure_test_iff, D.large_preimage_iff]

end Derivation
end IBLP.Extender
