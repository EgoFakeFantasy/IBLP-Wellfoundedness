import IBLP.Extender.SeedCollapse

namespace IBLP.Extender.Ultrapower
open FullMarkedBLP Derivation
universe u
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}
  (D : Derivation stage alpha beta) (ha : Order.IsSuccLimit alpha) (hb : Order.IsSuccLimit beta)

theorem seed_mem_constant (a : Seed stage beta) (x : Test stage alpha) :
    Mem D ha hb (seedObject D ha hb a) (constantEmbedding D ha hb (stage.rankInclude _ x)) ↔
      a.val ∈ (D.map x).val := by
  have constantEq : mk D ha hb ⟨a, Representative.constant (stage.rankInclude _ x)⟩ =
      constantEmbedding D ha hb (stage.rankInclude _ x) := ofComponent_constant D ha hb a _
  rw [← constantEq]
  change GlobalTruth.Holds D ha hb (.member 0 1)
    ![⟨a, identityRepresentative ha⟩, ⟨a, Representative.constant (stage.rankInclude _ x)⟩] ↔ _
  have common := GlobalTruth.same_seed D ha hb a (.member 0 1)
    ![identityRepresentative ha, Representative.constant (stage.rankInclude _ x)]
  have args : (fun i : Fin 2 => (⟨a, ![identityRepresentative ha,
      Representative.constant (stage.rankInclude _ x)] i⟩ : SeededRepresentative stage alpha beta)) =
      ![⟨a, identityRepresentative ha⟩, ⟨a, Representative.constant (stage.rankInclude _ x)⟩] := by
    funext i; fin_cases i <;> rfl
  rw [args] at common
  apply common.trans
  have same : formulaTest (.member 0 1)
      ![identityRepresentative ha, Representative.constant (stage.rankInclude _ x)] = x := by
    apply test_ext
    intro z
    rw [mem_formulaTest]
    change ((identityRepresentative ha).value z).val ∈
      ((Representative.constant (stage.rankInclude _ x)).value z).val ↔ z.val ∈ x.val
    rw [identityRepresentative_value, Representative.constant_value]
    rfl
  change D.Large a _ ↔ _
  rw [same]
  rfl

theorem predecessor_of_bounded_constant (x : Test stage alpha) (q : Ultrapower D ha hb)
    (edge : Mem D ha hb q (constantEmbedding D ha hb (stage.rankInclude _ x))) :
    ∃ a : Seed stage beta, q = seedObject D ha hb a := by
  rw [constantEmbedding_mk] at edge
  apply predecessor_is_seed D ha hb _ ?_ q edge
  intro z y hy
  rw [Representative.constant_value] at hy
  exact test_subset x hy

/-- Full agreement on the original saved successor-rank domain. This
includes every internal set of rank alpha, and the ordinal alpha itself. -/
theorem embedding_agrees
    (inaccessible : stage.model.InternalInaccessible (stage.ordinal beta)) (x : Test stage alpha) :
    (embedding D ha hb inaccessible (stage.rankInclude _ x)).val = (D.map x).val := by
  rw [embedding_val]
  apply ZFSet.ext
  intro z
  rw [mem_collapsedValue]
  constructor
  · rintro ⟨q, edge, valueEq⟩
    obtain ⟨a, rfl⟩ := predecessor_of_bounded_constant D ha hb x q edge
    have member := (seed_mem_constant D ha hb a x).mp edge
    rw [collapsed_seed] at valueEq
    rwa [← valueEq]
  · intro hz
    have inside := (stage.mem_hierarchy beta z).mp (test_subset (D.map x) hz)
    refine ⟨seedObject D ha hb ⟨z, inside⟩, (seed_mem_constant D ha hb _ x).mpr hz, ?_⟩
    exact collapsed_seed D ha hb inaccessible _

end IBLP.Extender.Ultrapower
