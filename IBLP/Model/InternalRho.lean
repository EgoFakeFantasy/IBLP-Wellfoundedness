import IBLP.Model.InternalWeakAction
import IBLP.Model.BoundedHierarchy

namespace IBLP
open FullMarkedBLP
universe u

namespace ModelStage

noncomputable def rho (stage : ModelStage.{u}) {alpha beta : Ordinal.{u}}
    (k : stage.BoundedMap alpha beta) (eta : Ordinal.{u}) : Ordinal.{u} :=
  (stage.rankOrdinalAction k (clippedOrdinal alpha eta)).val

theorem rho_monotone (stage : ModelStage.{u}) {alpha beta : Ordinal.{u}}
    (k : stage.BoundedMap alpha beta) : Monotone (stage.rho k) := by
  intro x y h
  exact (stage.rankOrdinalAction_strictMono k).monotone (min_le_min_left alpha h)

theorem rho_le (stage : ModelStage.{u}) {alpha beta : Ordinal.{u}}
    (k : stage.BoundedMap alpha beta) (eta : Ordinal.{u}) : stage.rho k eta ≤ beta :=
  Order.lt_succ_iff.mp (stage.rankOrdinalAction k (clippedOrdinal alpha eta)).property

theorem rho_of_source_le (stage : ModelStage.{u}) {alpha beta : Ordinal.{u}}
    (k : stage.BoundedMap alpha beta) {eta : Ordinal.{u}} (h : alpha ≤ eta) :
    stage.rho k eta = beta := by
  have he : clippedOrdinal alpha eta = endpoint alpha := Subtype.ext (min_eq_left h)
  unfold rho
  rw [he, stage.boundedMap_endpoint]
  rfl

theorem rho_inflationary (stage : ModelStage.{u}) {alpha beta : Ordinal.{u}}
    (k : stage.BoundedMap alpha beta) (eta : Ordinal.{u}) : min eta beta ≤ stage.rho k eta := by
  by_cases h : alpha ≤ eta
  · rw [stage.rho_of_source_le k h]
    exact min_le_right _ _
  · have hm : eta ≤ alpha := le_of_lt (lt_of_not_ge h)
    have hi := stage.rankOrdinalAction_inflationary k (clippedOrdinal alpha eta)
    change min alpha eta ≤ stage.rho k eta at hi
    rw [min_eq_right hm] at hi
    exact (min_le_left _ _).trans hi

theorem rho_min (stage : ModelStage.{u}) {alpha beta : Ordinal.{u}}
    (k : stage.BoundedMap alpha beta) (x y : Ordinal.{u}) :
    stage.rho k (min x y) = min (stage.rho k x) (stage.rho k y) := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, min_eq_left (stage.rho_monotone k h)]
  · rw [min_eq_right h, min_eq_right (stage.rho_monotone k h)]

theorem rho_strictMonoOn (stage : ModelStage.{u}) {alpha beta : Ordinal.{u}}
    (k : stage.BoundedMap alpha beta) : StrictMonoOn (stage.rho k) (Set.Iic alpha) := by
  intro x hx y hy hxy
  change x ≤ alpha at hx
  change y ≤ alpha at hy
  apply stage.rankOrdinalAction_strictMono k
  change min alpha x < min alpha y
  simpa only [min_eq_right hx, min_eq_right hy] using hxy

theorem rankCut_ordinal (stage : ModelStage.{u}) (alpha eta : Ordinal.{u}) :
    stage.rankCut alpha (stage.ordinal eta) = stage.rankOrdinal (clippedOrdinal alpha eta) := by
  apply Subtype.ext
  apply ZFSet.ext
  intro x
  rw [stage.rankCut_val, stage.rankOrdinal_val, ZFSet.mem_inter, ZFSet.mem_vonNeumann]
  change (x ∈ eta.toZFSet ∧ x.rank < alpha) ↔ x ∈ (min alpha eta).toZFSet
  constructor
  · rintro ⟨hm, hr⟩
    obtain ⟨gamma, hg, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hm
    rw [Ordinal.rank_toZFSet] at hr
    exact Ordinal.toZFSet_mem_toZFSet_iff.mpr (lt_min hr hg)
  · intro hm
    obtain ⟨gamma, hg, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hm
    exact ⟨Ordinal.toZFSet_mem_toZFSet_iff.mpr (lt_of_lt_of_le hg (min_le_right _ _)),
      by simpa only [Ordinal.rank_toZFSet] using lt_of_lt_of_le hg (min_le_left _ _)⟩

/-- The rank action is the value of the actual weak map on every ordinal. -/
theorem weakAction_ordinal (stage : ModelStage.{u}) {alpha beta : Ordinal.{u}}
    (k : stage.BoundedMap alpha beta) (eta : Ordinal.{u}) :
    stage.weakAction k (stage.ordinal eta) = stage.ordinal (stage.rho k eta) := by
  unfold weakAction
  rw [stage.rankCut_ordinal]
  apply Subtype.ext
  exact stage.rankOrdinalAction_compat k (clippedOrdinal alpha eta)

end ModelStage
end IBLP
