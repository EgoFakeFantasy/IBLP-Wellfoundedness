import IBLP.Rank.BoundedGraph

namespace IBLP
open FullMarkedBLP

universe u

/-- 截断后的集合属于 V_(alpha+1)，包括秩恰好等于 alpha 的边界。 -/
noncomputable def truncate (alpha : Ordinal.{u}) (z : ZFSet.{u}) : RankDomain (Order.succ alpha) :=
  ⟨z ∩ ZFSet.vonNeumann alpha, Order.lt_succ_of_le
    (ZFSet.subset_vonNeumann.mp (fun _ hx => (ZFSet.mem_inter.mp hx).2))⟩

theorem truncate_rank_le (alpha : Ordinal.{u}) (z : ZFSet.{u}) :
    (truncate alpha z).val.rank ≤ alpha :=
  ZFSet.subset_vonNeumann.mp (fun _ hx => (ZFSet.mem_inter.mp hx).2)

theorem truncate_of_rank_le {alpha : Ordinal.{u}} {z : ZFSet.{u}} (h : z.rank ≤ alpha) :
    (truncate alpha z).val = z := by
  apply ZFSet.ext
  intro x
  change x ∈ z ∩ ZFSet.vonNeumann alpha ↔ x ∈ z
  rw [ZFSet.mem_inter]
  exact ⟨And.left, fun hx => ⟨hx, ZFSet.subset_vonNeumann.mpr h hx⟩⟩

theorem truncate_truncate (alpha beta : Ordinal.{u}) (z : ZFSet.{u}) :
    (truncate alpha (truncate beta z).val).val = (truncate (min alpha beta) z).val := by
  apply ZFSet.ext
  intro x
  change x ∈ (z ∩ ZFSet.vonNeumann beta) ∩ ZFSet.vonNeumann alpha ↔
    x ∈ z ∩ ZFSet.vonNeumann (min alpha beta)
  simp only [ZFSet.mem_inter, ZFSet.mem_vonNeumann, lt_min_iff]
  tauto

abbrev BoundedMap (alpha beta : Ordinal.{u}) :=
  FirstOrder.Language.ElementaryEmbedding membershipLanguage
    (RankDomain (Order.succ alpha)) (RankDomain (Order.succ beta))

/-- 正文 K#(z)=K(z∩V_alpha)。输入是任意集合，而非仅原保存域元素。 -/
noncomputable def weakAction {alpha beta : Ordinal.{u}} (k : BoundedMap alpha beta)
    (z : ZFSet.{u}) : ZFSet.{u} := (k (truncate alpha z)).val

theorem weakAction_rank_le {alpha beta : Ordinal.{u}} (k : BoundedMap alpha beta)
    (z : ZFSet.{u}) : (weakAction k z).rank ≤ beta :=
  Order.lt_succ_iff.mp (k (truncate alpha z)).property

theorem weakAction_on_domain {alpha beta : Ordinal.{u}} (k : BoundedMap alpha beta)
    (x : RankDomain (Order.succ alpha)) : weakAction k x.val = (k x).val := by
  have same : truncate alpha x.val = x :=
    Subtype.ext (truncate_of_rank_le (Order.lt_succ_iff.mp x.property))
  unfold weakAction
  rw [same]

theorem weakAction_truncate {alpha beta gamma : Ordinal.{u}} (k : BoundedMap alpha beta)
    (h : alpha ≤ gamma) (z : ZFSet.{u}) :
    weakAction k (truncate gamma z).val = weakAction k z := by
  have same : truncate alpha (truncate gamma z).val = truncate alpha z := by
    apply Subtype.ext
    rw [truncate_truncate, min_eq_left h]
  unfold weakAction
  rw [same]

/-- 单图在较小保存域上的一致性推出对应的全输入截断等式。 -/
theorem weakAction_restriction {alpha beta delta epsilon : Ordinal.{u}}
    (k : BoundedMap alpha beta) (small : BoundedMap delta epsilon) (h : delta ≤ alpha)
    (agree : ∀ x : RankDomain (Order.succ delta),
      (small x).val = (k (rankInclude (Order.succ_le_succ h) x)).val) (z : ZFSet.{u}) :
    weakAction small z = weakAction k (truncate delta z).val := by
  rw [weakAction, agree]
  exact (weakAction_on_domain k (rankInclude (Order.succ_le_succ h) (truncate delta z))).symm

end IBLP
