import IBLP.Rank.BoundedHierarchy

namespace IBLP
open FullMarkedBLP

universe u

noncomputable def clippedOrdinal (alpha eta : Ordinal.{u}) : OrdinalDomain (Order.succ alpha) :=
  ⟨min alpha eta, Order.lt_succ_of_le (min_le_left _ _)⟩

noncomputable def rho {alpha beta : Ordinal.{u}} (k : BoundedMap alpha beta)
    (eta : Ordinal.{u}) : Ordinal.{u} := (ordinalAction k (clippedOrdinal alpha eta)).val

theorem rho_monotone {alpha beta : Ordinal.{u}} (k : BoundedMap alpha beta) : Monotone (rho k) := by
  intro x y h
  exact (ordinalAction_strictMono k).monotone (min_le_min_left alpha h)

theorem rho_le {alpha beta : Ordinal.{u}} (k : BoundedMap alpha beta) (eta : Ordinal.{u}) :
    rho k eta ≤ beta := Order.lt_succ_iff.mp (ordinalAction k (clippedOrdinal alpha eta)).property

theorem rho_of_source_le {alpha beta : Ordinal.{u}} (k : BoundedMap alpha beta)
    {eta : Ordinal.{u}} (h : alpha ≤ eta) : rho k eta = beta := by
  have he : clippedOrdinal alpha eta = endpoint alpha := Subtype.ext (min_eq_left h)
  unfold rho
  rw [he, boundedMap_endpoint]
  rfl

theorem rho_inflationary {alpha beta : Ordinal.{u}} (k : BoundedMap alpha beta) (eta : Ordinal.{u}) :
    min eta beta ≤ rho k eta := by
  by_cases h : alpha ≤ eta
  · rw [rho_of_source_le k h]
    exact min_le_right _ _
  · have hm : eta ≤ alpha := le_of_lt (lt_of_not_ge h)
    have hi := ordinalAction_inflationary k (clippedOrdinal alpha eta)
    change min alpha eta ≤ rho k eta at hi
    rw [min_eq_right hm] at hi
    exact (min_le_left _ _).trans hi

theorem rho_min {alpha beta : Ordinal.{u}} (k : BoundedMap alpha beta) (x y : Ordinal.{u}) :
    rho k (min x y) = min (rho k x) (rho k y) := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, min_eq_left (rho_monotone k h)]
  · rw [min_eq_right h, min_eq_right (rho_monotone k h)]

/-- 主稿 (3.6)。输入截断可以精确移过有界映射，输出界由 rho 给出。 -/
theorem weakAction_cut_commute {alpha beta : Ordinal.{u}} (ha : Order.IsSuccLimit alpha)
    (k : BoundedMap alpha beta) (eta : Ordinal.{u}) (z : ZFSet.{u}) :
    weakAction k (truncate eta z).val = (truncate (rho k eta) (weakAction k z)).val := by
  have same : truncate alpha (truncate eta z).val =
      rankIntersection (truncate alpha z) (rankHierarchy (clippedOrdinal alpha eta)) := by
    apply Subtype.ext
    apply ZFSet.ext
    intro x
    simp only [truncate, rankIntersection, rankHierarchy, clippedOrdinal,
      ZFSet.mem_inter, ZFSet.mem_vonNeumann, lt_min_iff]
    tauto
  unfold weakAction
  rw [same, rankMap_intersection, boundedMap_hierarchy ha]
  rfl

/-- 主稿 (3.7)，现在不再把逐点限制等式当作完整截断结论。 -/
theorem weakAction_restriction_cut {alpha beta delta epsilon : Ordinal.{u}}
    (ha : Order.IsSuccLimit alpha) (k : BoundedMap alpha beta) (small : BoundedMap delta epsilon)
    (h : delta ≤ alpha)
    (agree : ∀ x : RankDomain (Order.succ delta),
      (small x).val = (k (rankInclude (Order.succ_le_succ h) x)).val) (z : ZFSet.{u}) :
    weakAction small z = (truncate (rho k delta) (weakAction k z)).val := by
  rw [weakAction_restriction k small h agree, weakAction_cut_commute ha]

end IBLP
