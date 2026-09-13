import IBLP.Extender.UltrapowerCoherence
import IBLP.Model.GraphEqualizer

namespace IBLP.Extender.Derivation
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}

noncomputable def indexAgreement (p q : IndexMap stage alpha) : Test stage alpha :=
  subsetTest top (stage.graphEqualizer (stage.hierarchy alpha)
    (stage.rankInclude _ p.graph) (stage.rankInclude _ q.graph)) (by
      intro x hx
      rw [stage.graphEqualizer_val, ZFSet.mem_sep] at hx
      exact hx.1)

theorem indexAgreement_val (p q : IndexMap stage alpha) :
    (indexAgreement p q).val = ZFSet.sep
      (fun x => ∃ y, ZFSet.pair x y ∈ p.graph.val ∧ ZFSet.pair x y ∈ q.graph.val)
      (stage.hierarchy alpha).val := stage.graphEqualizer_val _ _ _

theorem mem_indexAgreement (p q : IndexMap stage alpha) (x : Seed stage alpha) :
    x.val ∈ (indexAgreement p q).val ↔ Representative.indexValue p x = Representative.indexValue q x := by
  rw [indexAgreement_val, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, y, hp, hq⟩
    apply Subtype.ext
    exact ((p.function.2 x.val ((stage.mem_hierarchy alpha x.val).mpr x.property)).unique
      (Representative.indexValue_edge p x) hp).trans
      ((q.function.2 x.val ((stage.mem_hierarchy alpha x.val).mpr x.property)).unique
        hq (Representative.indexValue_edge q x))
  · intro same
    refine ⟨(stage.mem_hierarchy alpha x.val).mpr x.property,
      (Representative.indexValue p x).val, Representative.indexValue_edge p x, ?_⟩
    rw [same]
    exact Representative.indexValue_edge q x

theorem map_indexAgreement_val (D : Derivation stage alpha beta) (p q : IndexMap stage alpha) :
    (D.map (indexAgreement p q)).val = ZFSet.sep
      (fun x => ∃ y, ZFSet.pair x y ∈ (D.map p.graph).val ∧ ZFSet.pair x y ∈ (D.map q.graph).val)
      (stage.hierarchy beta).val := by
  have h := (D.map.equalizer_iff top p.graph q.graph (indexAgreement p q)).mpr (indexAgreement_val p q)
  change (D.map (indexAgreement p q)).val = ZFSet.sep _
    (D.map (stage.rankHierarchy (endpoint alpha))).val at h
  rwa [stage.boundedMap_top] at h

theorem large_indexAgreement_iff (D : Derivation stage alpha beta) (seed : Seed stage beta)
    (p q : IndexMap stage alpha) :
    D.Large seed (indexAgreement p q) ↔ D.project p seed = D.project q seed := by
  change seed.val ∈ (D.map (indexAgreement p q)).val ↔ _
  rw [D.map_indexAgreement_val, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, y, hp, hq⟩
    exact Subtype.ext ((D.project_unique p seed y hp).symm.trans (D.project_unique q seed y hq))
  · intro same
    refine ⟨(stage.mem_hierarchy beta seed.val).mpr seed.property,
      (D.project p seed).val, D.project_edge p seed, ?_⟩
    rw [same]
    exact D.project_edge q seed

/-- Two internal projections with the same value at the target seed give
the same pulled-back representative, modulo the actual derived measure. -/
theorem pullback_equivalent_of_project_eq (D : Derivation stage alpha beta) (seed : Seed stage beta)
    (p q : IndexMap stage alpha) (same : D.project p seed = D.project q seed)
    (f : Representative stage alpha) : D.RepEquivalent seed (f.pullback p) (f.pullback q) := by
  apply D.large_mono seed (x := indexAgreement p q)
  · apply test_subset_of_pointwise
    intro x hx
    apply (mem_equalityTest _ _ x).mpr
    rw [Representative.pullback_value, Representative.pullback_value, (mem_indexAgreement p q x).mp hx]
  · exact (D.large_indexAgreement_iff seed p q).mpr same

theorem pullback_comp_equivalent (D : Derivation stage alpha beta) (seed : Seed stage beta)
    (ha : Order.IsSuccLimit alpha) (f : Representative stage alpha) (p q : IndexMap stage alpha) :
    D.RepEquivalent seed ((f.pullback q).pullback p) (f.pullback (p.comp ha q)) := by
  apply D.holds_of_pointwise
  intro x
  change ((f.pullback q).pullback p).value x = (f.pullback (p.comp ha q)).value x
  simp only [Representative.pullback_value, Representative.indexValue_comp]

end IBLP.Extender.Derivation
