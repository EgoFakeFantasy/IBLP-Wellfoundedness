import IBLP.Rank.WeakAgreement

namespace IBLP
open FullMarkedBLP

universe u v

theorem rho_restriction {alpha beta delta epsilon : Ordinal.{u}}
    (k : BoundedMap alpha beta) (small : BoundedMap delta epsilon) (h : delta ≤ alpha)
    (agree : ∀ x : RankDomain (Order.succ delta),
      (small x).val = (k (rankInclude (Order.succ_le_succ h) x)).val) (eta : Ordinal.{u}) :
    rho small eta = rho k (min delta eta) := by
  have point : rankInclude (Order.succ_le_succ h) (ordinalDomainElement (clippedOrdinal delta eta)) =
      ordinalDomainElement (clippedOrdinal alpha (min delta eta)) := by
    apply Subtype.ext
    simp only [rankInclude, ordinalDomainElement, clippedOrdinal,
      min_eq_right ((min_le_left delta eta).trans h)]
  have he := congrArg ZFSet.rank (agree (ordinalDomainElement (clippedOrdinal delta eta)))
  rw [point] at he
  exact he

theorem restriction_endpoint {alpha beta delta epsilon : Ordinal.{u}}
    (k : BoundedMap alpha beta) (small : BoundedMap delta epsilon) (h : delta ≤ alpha)
    (agree : ∀ x : RankDomain (Order.succ delta),
      (small x).val = (k (rankInclude (Order.succ_le_succ h) x)).val) :
    epsilon = rho k delta := by
  have he := rho_restriction k small h agree delta
  simpa only [rho_of_source_le small (le_refl delta), min_self] using he

/-- 每个字段都记录实际限制产生的等式，复合后自然界仍精确。 -/
structure CutRestriction {S : Type v} {C : CutSpace.{u} S} (small big : CutAction C) : Prop where
  bound_le : small.bound ≤ big.bound
  act_eq : ∀ z, small.act z = C.cut small.bound (big.act z)
  rho_eq : ∀ eta, small.rho eta = min (big.rho eta) small.bound

namespace CutRestriction

variable {S : Type v} {C : CutSpace.{u} S}

theorem refl (F : CutAction C) : CutRestriction F F where
  bound_le := le_refl _
  act_eq := fun z => (C.cut_eq_self (F.output_rank_le z)).symm
  rho_eq := fun eta => (min_eq_left (F.rho_le_bound eta)).symm

theorem comp {F F' G G' : CutAction C} (hf : CutRestriction F' F) (hg : CutRestriction G' G) :
    CutRestriction (F'.comp G') (F.comp G) where
  bound_le := by
    change F'.rho G'.bound ≤ F.rho G.bound
    rw [hf.rho_eq]
    exact (min_le_left _ _).trans (F.monotone hg.bound_le)
  act_eq := by
    intro z
    change F'.act (G'.act z) = C.cut (F'.rho G'.bound) (F.act (G.act z))
    rw [hf.act_eq, hg.act_eq, F.cut_commute, C.cut_cut, hf.rho_eq]
    rw [min_comm F'.bound (F.rho G'.bound)]
  rho_eq := by
    intro eta
    simp only [CutAction.comp_rho, CutAction.comp_bound, hf.rho_eq, hg.rho_eq, F.rho_min, min_assoc]

/-- 主稿 (3.10) 的递归式：限制界取当前因子的界与外侧 rho 作用后缀界之最小值。 -/
theorem comp_bound {F F' G' : CutAction C} (hf : CutRestriction F' F) :
    (F'.comp G').bound = min F'.bound (F.rho G'.bound) := by
  rw [CutAction.comp_bound, hf.rho_eq, min_comm]

theorem word {F F' : CutAction C} (hf : CutRestriction F' F)
    {tail' tail : List (CutAction C)} (ht : List.Forall₂ CutRestriction tail' tail) :
    CutRestriction (CutAction.word F' tail') (CutAction.word F tail) := by
  induction ht generalizing F F' with
  | nil => exact hf
  | @cons G' G gs' gs hg _ ih => exact hf.comp (ih hg)

/-- 同时缩小双方保存域时，弱相等保留在两个新自然顶界以下。 -/
theorem agreement {F F' G G' : CutAction C} (hf : CutRestriction F' F) (hg : CutRestriction G' G)
    {delta epsilon : Ordinal.{u}} (h : CutAction.AllInputAgreement F G delta)
    (he : epsilon ≤ delta) (hfBound : epsilon ≤ F'.bound) (hgBound : epsilon ≤ G'.bound) :
    CutAction.AllInputAgreement F' G' epsilon := by
  intro z
  rw [hf.act_eq, hg.act_eq, C.cut_lower hfBound, C.cut_lower hgBound]
  exact h.shrink he z

end CutRestriction

theorem boundedCutAction_restriction {alpha beta delta epsilon : Ordinal.{u}}
    (ha : Order.IsSuccLimit alpha) (hd : Order.IsSuccLimit delta)
    (k : BoundedMap alpha beta) (small : BoundedMap delta epsilon) (h : delta ≤ alpha)
    (agree : ∀ x : RankDomain (Order.succ delta),
      (small x).val = (k (rankInclude (Order.succ_le_succ h) x)).val) :
    CutRestriction (boundedCutAction hd small) (boundedCutAction ha k) where
  bound_le := by
    change epsilon ≤ beta
    rw [restriction_endpoint k small h agree]
    exact rho_le k delta
  act_eq := by
    intro z
    change weakAction small z = (truncate epsilon (weakAction k z)).val
    calc
      weakAction small z = (truncate (rho k delta) (weakAction k z)).val :=
        weakAction_restriction_cut ha k small h agree z
      _ = (truncate epsilon (weakAction k z)).val := by rw [← restriction_endpoint k small h agree]
  rho_eq := by
    intro eta
    change rho small eta = min (rho k eta) epsilon
    rw [rho_restriction k small h agree, IBLP.rho_min, ← restriction_endpoint k small h agree, min_comm]

end IBLP
