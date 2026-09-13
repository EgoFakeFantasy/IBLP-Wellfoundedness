import IBLP.Rank.CutSpace

namespace IBLP

universe u v

/-- 截断作用及其已证明的代数性质。不是初等性或 extender 的替代假设。 -/
structure CutAction {S : Type v} (C : CutSpace.{u} S) where
  act : S → S
  rho : Ordinal.{u} → Ordinal.{u}
  bound : Ordinal.{u}
  output_rank_le : ∀ z, C.rank (act z) ≤ bound
  monotone : Monotone rho
  rho_le_bound : ∀ eta, rho eta ≤ bound
  inflationary : ∀ eta, min eta bound ≤ rho eta
  cut_commute : ∀ eta z, act (C.cut eta z) = C.cut (rho eta) (act z)

noncomputable def boundedCutAction {alpha beta : Ordinal.{u}} (ha : Order.IsSuccLimit alpha)
    (k : BoundedMap alpha beta) : CutAction zfCutSpace where
  act := weakAction k
  rho := IBLP.rho k
  bound := beta
  output_rank_le := weakAction_rank_le k
  monotone := rho_monotone k
  rho_le_bound := rho_le k
  inflationary := rho_inflationary k
  cut_commute := weakAction_cut_commute ha k

namespace CutAction

variable {S : Type v} {C : CutSpace.{u} S}

theorem rho_of_bound_le (F : CutAction C) {eta : Ordinal.{u}} (h : F.bound ≤ eta) :
    F.rho eta = F.bound := by
  apply le_antisymm (F.rho_le_bound eta)
  simpa only [min_eq_right h] using F.inflationary eta

theorem rho_min (F : CutAction C) (alpha beta : Ordinal.{u}) :
    F.rho (min alpha beta) = min (F.rho alpha) (F.rho beta) := by
  rcases le_total alpha beta with h | h
  · rw [min_eq_left h, min_eq_left (F.monotone h)]
  · rw [min_eq_right h, min_eq_right (F.monotone h)]

/-- 非空有限词的归纳步，界从最右目标沿左侧 rho 计算，正是 (3.8)。 -/
def comp (F G : CutAction C) : CutAction C where
  act := F.act ∘ G.act
  rho := F.rho ∘ G.rho
  bound := F.rho G.bound
  output_rank_le := by
    intro z
    have he := F.cut_commute G.bound (G.act z)
    rw [C.cut_eq_self (G.output_rank_le z)] at he
    change C.rank (F.act (G.act z)) ≤ _
    rw [he]
    exact C.cut_rank_le _ _
  monotone := F.monotone.comp G.monotone
  rho_le_bound := fun eta => F.monotone (G.rho_le_bound eta)
  inflationary := by
    intro eta
    change min eta (F.rho G.bound) ≤ F.rho (G.rho eta)
    by_cases h : eta ≤ G.bound
    · have hg : eta ≤ G.rho eta := by simpa only [min_eq_left h] using G.inflationary eta
      exact (min_le_min hg (F.rho_le_bound G.bound)).trans (F.inflationary (G.rho eta))
    · rw [G.rho_of_bound_le (le_of_lt (lt_of_not_ge h))]
      exact min_le_right _ _
  cut_commute := by
    intro eta z
    change F.act (G.act (C.cut eta z)) = _
    rw [G.cut_commute, F.cut_commute]
    rfl

/-- 一个 head 与可能为空的 tail，明确排除没有自然有限顶界的恒等词。 -/
def word (head : CutAction C) : List (CutAction C) → CutAction C
  | [] => head
  | next :: rest => head.comp (word next rest)

theorem comp_act (F G : CutAction C) (z : S) : (F.comp G).act z = F.act (G.act z) := rfl
theorem comp_rho (F G : CutAction C) (eta : Ordinal.{u}) : (F.comp G).rho eta = F.rho (G.rho eta) := rfl
theorem comp_bound (F G : CutAction C) : (F.comp G).bound = F.rho G.bound := rfl

end CutAction
end IBLP
