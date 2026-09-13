import IBLP.Rank.WordRestriction

namespace IBLP
universe u v

/-- 非空有限列的最小值，不以任意默认序数填充空列。 -/
noncomputable def minimumBounds (head : Ordinal.{u}) : List Ordinal.{u} → Ordinal.{u}
  | [] => head
  | next :: rest => min head (minimumBounds next rest)

theorem minimumBounds_le_iff (eta head : Ordinal.{u}) (tail : List Ordinal.{u}) :
    eta ≤ minimumBounds head tail ↔ eta ≤ head ∧ ∀ x ∈ tail, eta ≤ x := by
  induction tail generalizing head with
  | nil => simp [minimumBounds]
  | cons x xs ih => simp [minimumBounds, ih]

namespace CutAction
variable {S : Type v} {C : CutSpace.{u} S}

theorem minimumBounds_map (F : CutAction C) (head : Ordinal.{u}) (tail : List Ordinal.{u}) :
    minimumBounds (F.rho head) (tail.map F.rho) = F.rho (minimumBounds head tail) := by
  induction tail generalizing head with
  | nil => rfl
  | cons x xs ih => simp only [minimumBounds, List.map_cons, ih, F.rho_min]

/-- 第 i 项是此前全部外侧 rho 的复合作用于第 i 个缩限目标。
最外侧因子的自身缩限目标由 minimumBounds 的 head 单独保存。 -/
def outerRestrictionBounds (F : CutAction C) : List (CutAction C × Ordinal.{u}) → List Ordinal.{u}
  | [] => []
  | (G, beta) :: rest => F.rho beta :: (outerRestrictionBounds G rest).map F.rho

end CutAction

namespace CutRestriction
variable {S : Type v} {C : CutSpace.{u} S}

/-- (3.10) 的展开式：自然界等于所有前缀输送后的缩限目标之最小值。 -/
theorem word_bound_prefix_min {F F' : CutAction C} (hf : CutRestriction F' F)
    {tail' tail : List (CutAction C)} (ht : List.Forall₂ CutRestriction tail' tail) :
    (CutAction.word F' tail').bound = minimumBounds F'.bound
      (F.outerRestrictionBounds (tail.zip (tail'.map CutAction.bound))) := by
  induction ht generalizing F F' with
  | nil => rfl
  | @cons G' G gs' gs hg _ ih =>
    change (F'.comp (CutAction.word G' gs')).bound = _
    rw [hf.comp_bound, ih hg]
    simp only [List.map_cons, List.zip_cons_cons, CutAction.outerRestrictionBounds, minimumBounds]
    rw [← F.minimumBounds_map]

end CutRestriction
end IBLP
