import IBLP.Rank.WeakAgreement

namespace IBLP
universe u v

/-- 用于读取序数边的实际成员结构，独立于某个外部全域 owner。 -/
structure OrdinalView {S : Type v} (C : CutSpace.{u} S) where
  elem : Ordinal.{u} → S
  rank_elem : ∀ a, C.rank (elem a) = a
  mem_elem : ∀ a b, C.mem (elem a) (elem b) ↔ a < b

noncomputable def zfOrdinalView : OrdinalView zfCutSpace where
  elem := Ordinal.toZFSet
  rank_elem := Ordinal.rank_toZFSet
  mem_elem := fun _ _ => Ordinal.toZFSet_mem_toZFSet_iff

namespace CutAction
variable {S : Type v} {C : CutSpace.{u} S}

theorem AllInputAgreement.mem {F G : CutAction C} {delta : Ordinal.{u}}
    (h : AllInputAgreement F G delta) {x : S} (hx : C.rank x < delta) (z : S) :
    C.mem x (F.act z) ↔ C.mem x (G.act z) := by
  have he : C.mem x (C.cut delta (F.act z)) ↔ C.mem x (C.cut delta (G.act z)) :=
    Iff.of_eq (congrArg (C.mem x) (h z))
  simpa only [C.mem_cut, hx, and_true] using he

/-- 任意输入 z 均可读取；只需已知一边的序数输出低于截断界。 -/
theorem AllInputAgreement.ordinal_value (O : OrdinalView C) {F G : CutAction C}
    {delta a b : Ordinal.{u}} (h : AllInputAgreement F G delta) (z : S)
    (hf : F.act z = O.elem a) (hg : G.act z = O.elem b) (ha : a < delta) : a = b := by
  have sections : ∀ t, t < delta → (t < a ↔ t < b) := by
    intro t ht
    have hm := h.mem (x := O.elem t) (by simpa only [O.rank_elem] using ht) z
    rw [hf, hg, O.mem_elem, O.mem_elem] at hm
    exact hm
  rcases lt_trichotomy a b with hab | same | hba
  · exact False.elim (lt_irrefl a ((sections a ha).mpr hab))
  · exact same
  · exact False.elim (lt_irrefl b ((sections b (hba.trans ha)).mp hba))

theorem WeakAgreement.reads_edge (O : OrdinalView C) {F G : CutAction C}
    {delta target : Ordinal.{u}} (hd : Order.IsSuccLimit delta) (h : WeakAgreement F G delta)
    (z : S) (hf : F.act z = O.elem target) (hg : ∃ b, G.act z = O.elem b)
    (ht : target < delta) : G.act z = O.elem target := by
  obtain ⟨b, hb⟩ := hg
  have same := ((weakAgreement_iff_allInputs hd).mp h).ordinal_value O z hf hb ht
  simpa only [← same] using hb

theorem WeakAgreement.moves_ordinal (O : OrdinalView C) {F G : CutAction C}
    {delta c image : Ordinal.{u}} (hd : Order.IsSuccLimit delta) (h : WeakAgreement F G delta)
    (hc : c < delta) (hf : F.act (O.elem c) = O.elem image) (hmoved : c < image) :
    G.act (O.elem c) ≠ O.elem c := by
  intro hfix
  have hm := ((weakAgreement_iff_allInputs hd).mp h).mem
    (x := O.elem c) (by simpa only [O.rank_elem] using hc) (O.elem c)
  rw [hf, hfix, O.mem_elem, O.mem_elem] at hm
  exact lt_irrefl c (hm.mp hmoved)

end CutAction
end IBLP
