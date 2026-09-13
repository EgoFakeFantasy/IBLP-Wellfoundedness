import IBLP.Extender.SeedObjects
import IBLP.Extender.CountablyClosed

namespace IBLP.Extender.Ultrapower
open FullMarkedBLP Derivation
universe u
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}
  (D : Derivation stage alpha beta) (ha : Order.IsSuccLimit alpha) (hb : Order.IsSuccLimit beta)
  (inaccessible : stage.model.InternalInaccessible (stage.ordinal beta))

theorem mem_collapsedValue (q : Ultrapower D ha hb) (z : ZFSet.{u}) :
    z ∈ collapsedValue D ha hb inaccessible q ↔
      ∃ p, Mem D ha hb p q ∧ collapsedValue D ha hb inaccessible p = z :=
  Extender.mem_collapse_iff (Mem D ha hb) (wellFounded D ha hb inaccessible) q z

/-- The identity representative at an arbitrary rank seed collapses to
the seed itself, proved by ambient membership induction. -/
theorem collapsed_seed (b : Seed stage beta) :
    collapsedValue D ha hb inaccessible (seedObject D ha hb b) = b.val := by
  have allSeeds : ∀ v : ZFSet.{u}, ∀ hv : v ∈ stage.model.carrier ∧ v.rank < beta,
      collapsedValue D ha hb inaccessible (seedObject D ha hb ⟨v, hv⟩) = v := by
    intro v
    induction v using ZFSet.mem_wf.induction with
    | h v ih =>
      intro hv
      apply ZFSet.ext
      intro z
      rw [mem_collapsedValue]
      constructor
      · rintro ⟨p, edge, valueEq⟩
        obtain ⟨a, rfl⟩ := predecessor_of_seed D ha hb ⟨v, hv⟩ p edge
        have member := (seed_mem_seed D ha hb a ⟨v, hv⟩).mp edge
        have seedEq : collapsedValue D ha hb inaccessible (seedObject D ha hb a) = a.val :=
          ih a.val member a.property
        rw [seedEq] at valueEq
        rwa [← valueEq]
      · intro hz
        have inside : z ∈ stage.model.carrier ∧ z.rank < beta :=
          ⟨stage.model.transitive hz hv.1, (ZFSet.rank_lt_of_mem hz).trans hv.2⟩
        refine ⟨seedObject D ha hb ⟨z, inside⟩, (seed_mem_seed D ha hb _ _).mpr hz, ?_⟩
        exact ih z hz inside
  exact allSeeds b.val b.property

theorem seed_in_target (b : Seed stage beta) : b.val ∈ (target D ha hb inaccessible).carrier := by
  have h := (collapseMap D ha hb inaccessible (seedObject D ha hb b)).property
  change collapsedValue D ha hb inaccessible (seedObject D ha hb b) ∈ _ at h
  rwa [collapsed_seed] at h

end IBLP.Extender.Ultrapower
