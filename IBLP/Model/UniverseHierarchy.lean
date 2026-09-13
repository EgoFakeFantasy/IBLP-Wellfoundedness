import IBLP.Model.Graph
import FullMarkedBLP.RankHierarchyGraph

namespace IBLP
open FullMarkedBLP
universe u

/-- 环境累计层序列的真实集合图。构造不要求把 upper 放进某个极限秩。 -/
noncomputable def universeHierarchyGraph (upper : Ordinal.{u}) : ZFSet.{u} :=
  zfFunctionGraph (rankHierarchyMember (endpoint upper))

theorem universeHierarchyGraph_function (upper : Ordinal.{u}) :
    ZFSet.IsFunc upper.toZFSet (ZFSet.vonNeumann upper) (universeHierarchyGraph upper) :=
  zfFunctionGraph_isFunc (rankHierarchyMember (endpoint upper))

theorem universeHierarchyGraph_applies (upper : Ordinal.{u}) (i value : ZFSet.{u}) :
    ZFSet.pair i value ∈ universeHierarchyGraph upper ↔
      i ∈ upper.toZFSet ∧ value = ZFSet.vonNeumann i.rank := by
  rw [universeHierarchyGraph, mem_zfFunctionGraph]
  constructor
  · rintro ⟨hi, hv⟩
    exact ⟨hi, hv.symm⟩
  · rintro ⟨hi, hv⟩
    exact ⟨hi, hv.symm⟩

theorem universeHierarchyGraph_at {upper beta : Ordinal.{u}} (h : beta < upper) :
    ZFSet.pair beta.toZFSet (ZFSet.vonNeumann beta) ∈ universeHierarchyGraph upper := by
  apply (universeHierarchyGraph_applies _ _ _).mpr
  exact ⟨Ordinal.toZFSet_mem_toZFSet_iff.mpr h, by rw [Ordinal.rank_toZFSet]⟩

theorem universeHierarchyGraph_recursion (upper : Ordinal.{u}) (i value : ZFSet.{u})
    (edge : ZFSet.pair i value ∈ universeHierarchyGraph upper) (z : ZFSet.{u}) :
    z ∈ value ↔ ∃ a b : ZFSet.{u}, a ∈ i ∧
      ZFSet.pair a b ∈ universeHierarchyGraph upper ∧ z ⊆ b := by
  obtain ⟨hi, hv⟩ := (universeHierarchyGraph_applies _ _ _).mp edge
  obtain ⟨beta, below, representation⟩ := Ordinal.mem_toZFSet_iff.mp hi
  rw [← representation, Ordinal.rank_toZFSet] at hv
  rw [hv, ← representation]
  constructor
  · intro hz
    obtain ⟨gamma, less, subset⟩ := ZFSet.mem_vonNeumann'.mp hz
    exact ⟨gamma.toZFSet, ZFSet.vonNeumann gamma,
      Ordinal.toZFSet_mem_toZFSet_iff.mpr less, universeHierarchyGraph_at (less.trans below), subset⟩
  · rintro ⟨a, b, smaller, applied, subset⟩
    have less : a.rank < beta := by
      simpa only [Ordinal.rank_toZFSet] using ZFSet.rank_lt_of_mem smaller
    have image := ((universeHierarchyGraph_applies _ _ _).mp applied).2
    exact ZFSet.mem_vonNeumann'.mpr ⟨a.rank, less, by simpa only [← image] using subset⟩

end IBLP
