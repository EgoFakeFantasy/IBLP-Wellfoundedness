import IBLP.Extender.CountableSeeds
import IBLP.Model.RelationSections

namespace IBLP.Extender.Derivation
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}

/-- A single actual relation S ⊆ omega × U, with rank at most alpha.
Only S and its individual sections, never the higher-rank test sequence,
are submitted to the original bounded elementary map. -/
noncomputable def countableRelationTest (ha : Order.IsSuccLimit alpha) (tests : Nat → Test stage alpha) :
    Test stage alpha :=
  let S := stage.countableRelation (fun n => stage.rankInclude _ (tests n))
  ⟨S.val, S.property, Order.lt_succ_of_le (graph_rank_le_limit ha (x := Ordinal.omega0.toZFSet)
    (by simpa using Ordinal.omega0_le_of_isSuccLimit ha) (stage.hierarchy_rank alpha).le (by
      intro p hp
      obtain ⟨n, x, hx, rfl⟩ := (stage.mem_countableRelation _ p).mp hp
      exact ZFSet.pair_mem_prod.mpr ⟨(natZFSetOmegaEquiv n).property, test_subset (tests n) hx⟩))⟩

theorem countableRelationTest_edge_iff (ha : Order.IsSuccLimit alpha) (tests : Nat → Test stage alpha)
    (n : Nat) (x : ZFSet.{u}) :
    ZFSet.pair (n : Ordinal.{u}).toZFSet x ∈ (countableRelationTest ha tests).val ↔ x ∈ (tests n).val :=
  stage.countableRelation_edge_iff _ n x

theorem map_countableRelationTest_edge_iff (D : Derivation stage alpha beta)
    (ha : Order.IsSuccLimit alpha) (hb : Order.IsSuccLimit beta) (tests : Nat → Test stage alpha)
    (n : Nat) (x : Test stage beta) :
    ZFSet.pair (n : Ordinal.{u}).toZFSet x.val ∈ (D.map (countableRelationTest ha tests)).val ↔
      x.val ∈ (D.map (tests n)).val := by
  have source : (stage.model.rankPart (Order.succ alpha)).realize relationSectionMatrix
      ![naturalTest ha n, countableRelationTest ha tests, tests n] :=
    (relationSectionMatrix_realize _ _ _ _).mpr (fun z => (countableRelationTest_edge_iff ha tests n z).symm)
  have image := (D.map.realize_iff relationSectionMatrix
    ![naturalTest ha n, countableRelationTest ha tests, tests n]).mpr source
  have args : D.map ∘ ![naturalTest ha n, countableRelationTest ha tests, tests n] =
      ![D.map (naturalTest ha n), D.map (countableRelationTest ha tests), D.map (tests n)] := by
    funext i; fin_cases i <;> rfl
  rw [args, D.map_naturalTest ha hb, relationSectionMatrix_realize] at image
  exact (image x.val).symm

noncomputable def omegaIntersection (_ha : Order.IsSuccLimit alpha) (relation : Test stage alpha) : Test stage alpha :=
  subsetTest top (stage.relationIntersection (stage.hierarchy alpha) (stage.ordinal Ordinal.omega0)
    (stage.rankInclude _ relation)) (by
      intro z hz
      rw [stage.relationIntersection_val, ZFSet.mem_sep] at hz
      exact hz.1)

theorem omegaIntersection_val (ha : Order.IsSuccLimit alpha) (relation : Test stage alpha) :
    (omegaIntersection ha relation).val =
      ZFSet.sep (fun x => ∀ i ∈ Ordinal.omega0.toZFSet, ZFSet.pair i x ∈ relation.val) (stage.hierarchy alpha).val :=
  stage.relationIntersection_val _ _ _

theorem map_omegaIntersection_val (D : Derivation stage alpha beta)
    (ha : Order.IsSuccLimit alpha) (hb : Order.IsSuccLimit beta) (relation : Test stage alpha) :
    (D.map (omegaIntersection ha relation)).val =
      ZFSet.sep (fun x => ∀ i ∈ Ordinal.omega0.toZFSet, ZFSet.pair i x ∈ (D.map relation).val)
        (stage.hierarchy beta).val := by
  have source : (stage.model.rankPart (Order.succ alpha)).realize relationIntersectionMatrix
      ![top, omegaTest ha, relation, omegaIntersection ha relation] :=
    (relationIntersectionMatrix_realize _ _ _ _ _).mpr (omegaIntersection_val ha relation)
  have image := (D.map.realize_iff relationIntersectionMatrix
    ![top, omegaTest ha, relation, omegaIntersection ha relation]).mpr source
  have args : D.map ∘ ![top, omegaTest ha, relation, omegaIntersection ha relation] =
      ![D.map top, D.map (omegaTest ha), D.map relation, D.map (omegaIntersection ha relation)] := by
    funext i; fin_cases i <;> rfl
  rw [args, D.map_omegaTest ha hb, relationIntersectionMatrix_realize] at image
  change (D.map (omegaIntersection ha relation)).val = ZFSet.sep _
    (D.map (stage.rankHierarchy (endpoint alpha))).val at image
  rwa [stage.boundedMap_top] at image

theorem mem_countableIntersection (ha : Order.IsSuccLimit alpha) (tests : Nat → Test stage alpha) (z : ZFSet.{u}) :
    z ∈ (omegaIntersection ha (countableRelationTest ha tests)).val ↔
      z ∈ (stage.hierarchy alpha).val ∧ ∀ n, z ∈ (tests n).val := by
  rw [omegaIntersection_val, ZFSet.mem_sep, forall_omega_iff]
  simp only [countableRelationTest_edge_iff]

theorem large_countableIntersection_iff (D : Derivation stage alpha beta)
    (ha : Order.IsSuccLimit alpha) (hb : Order.IsSuccLimit beta) (seed : Seed stage beta)
    (tests : Nat → Test stage alpha) :
    D.Large seed (omegaIntersection ha (countableRelationTest ha tests)) ↔ ∀ n, D.Large seed (tests n) := by
  change seed.val ∈ (D.map _).val ↔ _
  rw [D.map_omegaIntersection_val ha hb, ZFSet.mem_sep, forall_omega_iff]
  let x : Test stage beta := ⟨seed.val, seed.property.1, seed.property.2.trans (Order.lt_succ beta)⟩
  constructor
  · rintro ⟨_, h⟩ n
    exact (D.map_countableRelationTest_edge_iff ha hb tests n x).mp (h n)
  · intro h
    exact ⟨(stage.mem_hierarchy beta seed.val).mpr seed.property,
      fun n => (D.map_countableRelationTest_edge_iff ha hb tests n x).mpr (h n)⟩

theorem countable_complete (D : Derivation stage alpha beta)
    (ha : Order.IsSuccLimit alpha) (hb : Order.IsSuccLimit beta) (seed : Seed stage beta)
    (tests : Nat → Test stage alpha) (large : ∀ n, D.Large seed (tests n)) :
    ∃ x : Seed stage alpha, ∀ n, x.val ∈ (tests n).val := by
  obtain ⟨z, hz⟩ := D.large_nonempty seed ((D.large_countableIntersection_iff ha hb seed tests).mpr large)
  obtain ⟨inside, allTests⟩ := (mem_countableIntersection ha tests z).mp hz
  exact ⟨⟨z, (stage.mem_hierarchy alpha z).mp inside⟩, allTests⟩

end IBLP.Extender.Derivation
