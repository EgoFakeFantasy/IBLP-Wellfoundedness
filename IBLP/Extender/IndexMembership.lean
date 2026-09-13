import IBLP.Extender.IndexRepresentative
import IBLP.Model.GraphMembership

namespace IBLP.Extender.Derivation
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}

noncomputable def indexMembership (p q : IndexMap stage alpha) : Test stage alpha :=
  subsetTest top (stage.graphMembership (stage.hierarchy alpha)
    (stage.rankInclude _ p.graph) (stage.rankInclude _ q.graph)) (by
      intro x hx
      rw [stage.graphMembership_val, ZFSet.mem_sep] at hx
      exact hx.1)

theorem indexMembership_val (p q : IndexMap stage alpha) :
    (indexMembership p q).val = ZFSet.sep (fun x => ∃ y z, ZFSet.pair x y ∈ p.graph.val ∧
      ZFSet.pair x z ∈ q.graph.val ∧ y ∈ z) (stage.hierarchy alpha).val := stage.graphMembership_val _ _ _

theorem mem_indexMembership (p q : IndexMap stage alpha) (x : Seed stage alpha) :
    x.val ∈ (indexMembership p q).val ↔
      (Representative.indexValue p x).val ∈ (Representative.indexValue q x).val := by
  rw [indexMembership_val, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, y, z, hp, hq, hm⟩
    have py := (p.function.2 x.val ((stage.mem_hierarchy alpha x.val).mpr x.property)).unique
      (Representative.indexValue_edge p x) hp
    have qz := (q.function.2 x.val ((stage.mem_hierarchy alpha x.val).mpr x.property)).unique
      (Representative.indexValue_edge q x) hq
    rwa [← py, ← qz] at hm
  · intro hm
    exact ⟨(stage.mem_hierarchy alpha x.val).mpr x.property,
      (Representative.indexValue p x).val, (Representative.indexValue q x).val,
      Representative.indexValue_edge p x, Representative.indexValue_edge q x, hm⟩

theorem map_indexMembership_val (D : Derivation stage alpha beta) (p q : IndexMap stage alpha) :
    (D.map (indexMembership p q)).val = ZFSet.sep (fun x => ∃ y z, ZFSet.pair x y ∈ (D.map p.graph).val ∧
      ZFSet.pair x z ∈ (D.map q.graph).val ∧ y ∈ z) (stage.hierarchy beta).val := by
  have h := (D.map.membershipTest_iff top p.graph q.graph (indexMembership p q)).mpr (indexMembership_val p q)
  change (D.map (indexMembership p q)).val = ZFSet.sep _
    (D.map (stage.rankHierarchy (endpoint alpha))).val at h
  rwa [stage.boundedMap_top] at h

theorem large_indexMembership_iff (D : Derivation stage alpha beta) (seed : Seed stage beta)
    (p q : IndexMap stage alpha) :
    D.Large seed (indexMembership p q) ↔ (D.project p seed).val ∈ (D.project q seed).val := by
  change seed.val ∈ (D.map (indexMembership p q)).val ↔ _
  rw [D.map_indexMembership_val, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, y, z, hp, hq, hm⟩
    rwa [D.project_unique p seed y hp, D.project_unique q seed z hq] at hm
  · intro hm
    exact ⟨(stage.mem_hierarchy beta seed.val).mpr seed.property,
      (D.project p seed).val, (D.project q seed).val, D.project_edge p seed, D.project_edge q seed, hm⟩

theorem holds_index_membership (D : Derivation stage alpha beta) (seed : Seed stage beta)
    (p q : IndexMap stage alpha) :
    D.Holds seed (.member 0 1) ![p.toRepresentative, q.toRepresentative] ↔
      (D.project p seed).val ∈ (D.project q seed).val := by
  have same : formulaTest (.member 0 1) ![p.toRepresentative, q.toRepresentative] = indexMembership p q := by
    apply test_ext
    intro x
    rw [mem_formulaTest, mem_indexMembership]
    change (p.toRepresentative.value x).val ∈ (q.toRepresentative.value x).val ↔ _
    rw [IndexMap.toRepresentative_value, IndexMap.toRepresentative_value]
    rfl
  change D.Large seed _ ↔ _
  rw [same, D.large_indexMembership_iff]

end IBLP.Extender.Derivation
