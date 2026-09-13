import IBLP.Model.HierarchyImage

namespace IBLP
open FullMarkedBLP FirstOrder Language
universe u

def modelSuccessorFormula : membershipLanguage.Formula (Fin 2) :=
  .all ((rankMemAt (.inr 0) (.inl 0)).iff
    ((BoundedFormula.equal (.var (.inr 0)) (.var (.inl 1))) ⊔ rankMemAt (.inr 0) (.inl 1)))

theorem TransitiveClass.successorFormula_realize (M : TransitiveClass.{u}) (s x : M.Element) :
    modelSuccessorFormula.Realize ![s, x] ↔ s.val = insert x.val x.val := by
  have semantic : modelSuccessorFormula.Realize ![s, x] ↔
      ∀ w : M.Element, w.val ∈ s.val ↔ w = x ∨ w.val ∈ x.val := by
    classical
    simp [modelSuccessorFormula, Formula.Realize, BoundedFormula.Realize,
      M.memAt_realize, Fin.snoc, imp_iff_not_or]
  rw [semantic]
  constructor
  · intro h
    apply ZFSet.ext
    intro w
    rw [ZFSet.mem_insert_iff]
    constructor
    · intro hw
      rcases (h (M.member s w hw)).mp hw with he | hm
      · exact Or.inl (congrArg Subtype.val he)
      · exact Or.inr hm
    · rintro (he | hm)
      · subst w
        exact (h x).mpr (Or.inl rfl)
      · exact (h (M.member x w hm)).mpr (Or.inr hm)
  · intro hs w
    rw [hs, ZFSet.mem_insert_iff]
    exact or_congr Subtype.val_inj Iff.rfl

/-- 后继保持由一个实际有限公式输送，免去像图端点的额外条件。 -/
theorem ModelStage.ordinalImage_succ (source : ModelStage.{u}) {N : TransitiveClass.{u}}
    (j : source.model.ElementaryMap N) (beta : Ordinal.{u}) :
    source.ordinalImage j (Order.succ beta) = Order.succ (source.ordinalImage j beta) := by
  have h := j.map_formula modelSuccessorFormula ![source.ordinal (Order.succ beta), source.ordinal beta]
  have tuple : j ∘ ![source.ordinal (Order.succ beta), source.ordinal beta] =
      ![j (source.ordinal (Order.succ beta)), j (source.ordinal beta)] := by
    funext i
    fin_cases i <;> rfl
  rw [tuple, N.successorFormula_realize, source.model.successorFormula_realize] at h
  have successorSet (a : Ordinal.{u}) : (Order.succ a).toZFSet = insert a.toZFSet a.toZFSet := by
    simpa only [Order.succ_eq_add_one] using Ordinal.toZFSet_add_one a
  have step := h.mpr (successorSet beta)
  rw [source.ordinalImage_compat, source.ordinalImage_compat, ← successorSet] at step
  simpa only [Ordinal.rank_toZFSet] using congrArg ZFSet.rank step

end IBLP
