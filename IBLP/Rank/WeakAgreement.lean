import IBLP.Rank.WordAction

namespace IBLP

universe u v

namespace CutAction

variable {S : Type v} {C : CutSpace.{u} S}

def WeakAgreement (F G : CutAction C) (delta : Ordinal.{u}) : Prop :=
  ∀ x z, C.rank x < delta → C.rank z < delta → (C.mem x (F.act z) ↔ C.mem x (G.act z))

def AllInputAgreement (F G : CutAction C) (delta : Ordinal.{u}) : Prop :=
  ∀ z, C.cut delta (F.act z) = C.cut delta (G.act z)

theorem membership_cut_input (F : CutAction C) (x z : S) (eta : Ordinal.{u})
    (hx : C.rank x < eta) : C.mem x (F.act z) ↔ C.mem x (F.act (C.cut eta z)) := by
  rw [F.cut_commute, C.mem_cut]
  constructor
  · intro h
    have hb : C.rank x < F.bound := (C.rank_mem_lt h).trans_le (F.output_rank_le z)
    exact ⟨h, (lt_min hx hb).trans_le (F.inflationary eta)⟩
  · exact And.left

theorem AllInputAgreement.weak {F G : CutAction C} {delta : Ordinal.{u}}
    (h : AllInputAgreement F G delta) : WeakAgreement F G delta := by
  intro x z hx _
  have he := congrArg (C.mem x) (h z)
  have hh : C.mem x (C.cut delta (F.act z)) ↔ C.mem x (C.cut delta (G.act z)) := Iff.of_eq he
  simpa only [C.mem_cut, hx, and_true] using hh

/-- 主稿 (3.11)。限制输入的弱相等能检验任意内部输入。 -/
theorem weakAgreement_iff_allInputs {F G : CutAction C} {delta : Ordinal.{u}}
    (hd : Order.IsSuccLimit delta) : WeakAgreement F G delta ↔ AllInputAgreement F G delta := by
  constructor
  · intro h z
    apply C.ext
    intro x
    rw [C.mem_cut, C.mem_cut]
    by_cases hx : C.rank x < delta
    · have he : Order.succ (C.rank x) < delta := hd.succ_lt hx
      have hi : C.rank x < Order.succ (C.rank x) := Order.lt_succ _
      have hz : C.rank (C.cut (Order.succ (C.rank x)) z) < delta := (C.cut_rank_le _ _).trans_lt he
      have hm := (F.membership_cut_input x z _ hi).trans
        ((h x _ hx hz).trans (G.membership_cut_input x z _ hi).symm)
      simpa only [hx, and_true] using hm
    · simp only [hx, and_false]
  · exact AllInputAgreement.weak

theorem AllInputAgreement.shrink {F G : CutAction C} {delta epsilon : Ordinal.{u}}
    (h : AllInputAgreement F G delta) (hle : epsilon ≤ delta) : AllInputAgreement F G epsilon := by
  intro z
  have he := congrArg (C.cut epsilon) (h z)
  simpa only [C.cut_lower hle] using he

theorem AllInputAgreement.comp_right {F G : CutAction C} {delta : Ordinal.{u}}
    (h : AllInputAgreement F G delta) (H : CutAction C) :
    AllInputAgreement (F.comp H) (G.comp H) delta := fun z => h (H.act z)

theorem AllInputAgreement.comp_left {F G : CutAction C} {delta : Ordinal.{u}}
    (h : AllInputAgreement F G delta) (H : CutAction C) :
    AllInputAgreement (H.comp F) (H.comp G) (H.rho delta) := by
  intro z
  have he := congrArg H.act (h z)
  simpa only [H.cut_commute] using he

theorem WeakAgreement.comp_right {F G : CutAction C} {delta : Ordinal.{u}}
    (hd : Order.IsSuccLimit delta) (h : WeakAgreement F G delta) (H : CutAction C) :
    WeakAgreement (F.comp H) (G.comp H) delta :=
  ((weakAgreement_iff_allInputs hd).mp h |>.comp_right H).weak

theorem WeakAgreement.comp_left {F G : CutAction C} {delta : Ordinal.{u}}
    (hd : Order.IsSuccLimit delta) (h : WeakAgreement F G delta) (H : CutAction C) :
    WeakAgreement (H.comp F) (H.comp G) (H.rho delta) :=
  ((weakAgreement_iff_allInputs hd).mp h |>.comp_left H).weak

end CutAction
end IBLP
