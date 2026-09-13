import IBLP.Model.SetRestriction
import IBLP.Model.InternalWeakTruncation
import IBLP.Model.SuccessorImage

namespace IBLP
open FullMarkedBLP FirstOrder Language
universe u

/-- Changing the proof of the domain equality leaves every set value intact. -/
def SetDomain.congr {left right : ZFSet.{u}} (same : left = right) :
    Language.Equiv membershipLanguage (SetDomain left) (SetDomain right) where
  toFun := fun x => ⟨x.val, same ▸ x.property⟩
  invFun := fun x => ⟨x.val, same.symm ▸ x.property⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_fun' := fun f => Empty.elim f
  map_rel' := by
    intro n r values
    obtain ⟨same⟩ := r
    subst n
    rfl

namespace ModelStage

def rankLift (stage : ModelStage.{u}) {lambda mu : Ordinal.{u}} (h : lambda ≤ mu)
    (x : stage.model.RankElement lambda) : stage.model.RankElement mu :=
  ⟨x.val, x.property.1, x.property.2.trans_le h⟩

def rankCongr (stage : ModelStage.{u}) {lambda mu : Ordinal.{u}} (same : lambda = mu) :
    Language.Equiv membershipLanguage (stage.model.RankElement lambda) (stage.model.RankElement mu) where
  toFun := fun x => ⟨x.val, x.property.1, same ▸ x.property.2⟩
  invFun := fun x => ⟨x.val, x.property.1, same.symm ▸ x.property.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_fun' := fun f => Empty.elim f
  map_rel' := by
    intro n r values
    obtain ⟨same⟩ := r
    subst n
    rfl

/-- Actual elementary restriction once the image of its internal domain set
has been identified. The map is not an added existence assumption. -/
noncomputable def rankRestrictOfImage (stage : ModelStage.{u}) {lambda mu : Ordinal.{u}}
    (k : (stage.model.rankPart lambda).ElementaryMap (stage.model.rankPart mu))
    (eta : OrdinalDomain lambda) (image : OrdinalDomain mu)
    (same : k (stage.rankHierarchy eta) = stage.rankHierarchy image) :
    (stage.model.rankPart eta.val).ElementaryMap (stage.model.rankPart image.val) :=
  (stage.rankDomainEquiv image.val).symm.toElementaryEmbedding.comp
    ((SetDomain.congr (congrArg Subtype.val same)).toElementaryEmbedding.comp
      ((k.restrictToSet (stage.rankHierarchy eta)).comp
        (stage.rankDomainEquiv eta.val).toElementaryEmbedding))

theorem rankRestrictOfImage_val (stage : ModelStage.{u}) {lambda mu : Ordinal.{u}}
    (k : (stage.model.rankPart lambda).ElementaryMap (stage.model.rankPart mu))
    (eta : OrdinalDomain lambda) (image : OrdinalDomain mu)
    (same : k (stage.rankHierarchy eta) = stage.rankHierarchy image)
    (x : stage.model.RankElement eta.val) :
    (stage.rankRestrictOfImage k eta image same x).val = (k (stage.rankLift eta.property.le x)).val := rfl

theorem rankOrdinalAction_succ (stage : ModelStage.{u}) {lambda mu : Ordinal.{u}}
    (k : (stage.model.rankPart lambda).ElementaryMap (stage.model.rankPart mu))
    (eta : Ordinal.{u}) (hs : Order.succ eta < lambda) :
    (stage.rankOrdinalAction k ⟨Order.succ eta, hs⟩).val =
      Order.succ (stage.rankOrdinalAction k ⟨eta, (Order.lt_succ eta).trans hs⟩).val := by
  let a : OrdinalDomain lambda := ⟨eta, (Order.lt_succ eta).trans hs⟩
  let s : OrdinalDomain lambda := ⟨Order.succ eta, hs⟩
  have h := k.map_formula modelSuccessorFormula ![stage.rankOrdinal s, stage.rankOrdinal a]
  have tuple : k ∘ ![stage.rankOrdinal s, stage.rankOrdinal a] =
      ![k (stage.rankOrdinal s), k (stage.rankOrdinal a)] := by
    funext i
    fin_cases i <;> rfl
  rw [tuple, (stage.model.rankPart mu).successorFormula_realize,
    (stage.model.rankPart lambda).successorFormula_realize] at h
  have successorSet (o : Ordinal.{u}) : (Order.succ o).toZFSet = insert o.toZFSet o.toZFSet := by
    simpa only [Order.succ_eq_add_one] using Ordinal.toZFSet_add_one o
  have step := h.mpr (successorSet eta)
  rw [stage.rankOrdinalAction_compat, stage.rankOrdinalAction_compat, ← successorSet] at step
  simpa only [Ordinal.rank_toZFSet] using congrArg ZFSet.rank step

/-- Restrict to a smaller successor rank. The endpoint case retains k itself. -/
theorem boundedRestrict_exists (stage : ModelStage.{u}) {alpha beta : Ordinal.{u}}
    (ha : Order.IsSuccLimit alpha) (k : stage.BoundedMap alpha beta)
    (delta : Ordinal.{u}) (hd : delta ≤ alpha) :
    ∃ small : stage.BoundedMap delta (stage.rho k delta),
      ∀ x, (small x).val = (k (stage.rankLift (Order.succ_le_succ hd) x)).val := by
  by_cases same : delta = alpha
  · subst delta
    rw [stage.rho_of_source_le k (le_refl alpha)]
    exact ⟨k, fun _ => rfl⟩
  · have lower : delta < alpha := lt_of_le_of_ne hd same
    let eta : OrdinalDomain (Order.succ alpha) :=
      ⟨Order.succ delta, (ha.succ_lt lower).trans (Order.lt_succ alpha)⟩
    let image : OrdinalDomain (Order.succ beta) := stage.rankOrdinalAction k eta
    have imageEq : image.val = Order.succ (stage.rho k delta) := by
      rw [stage.rankOrdinalAction_succ k delta eta.property]
      congr 1
      apply congrArg (fun o => (stage.rankOrdinalAction k o).val)
      exact Subtype.ext (min_eq_right hd).symm
    let restricted : (stage.model.rankPart (Order.succ delta)).ElementaryMap (stage.model.rankPart image.val) :=
      stage.rankRestrictOfImage k eta image (stage.boundedMap_hierarchy ha k eta)
    exact ⟨(stage.rankCongr imageEq).toElementaryEmbedding.comp restricted, fun _ => rfl⟩

noncomputable def boundedRestrict (stage : ModelStage.{u}) {alpha beta : Ordinal.{u}}
    (ha : Order.IsSuccLimit alpha) (k : stage.BoundedMap alpha beta)
    (delta : Ordinal.{u}) (hd : delta ≤ alpha) : stage.BoundedMap delta (stage.rho k delta) :=
  (stage.boundedRestrict_exists ha k delta hd).choose

theorem boundedRestrict_val (stage : ModelStage.{u}) {alpha beta : Ordinal.{u}}
    (ha : Order.IsSuccLimit alpha) (k : stage.BoundedMap alpha beta)
    (delta : Ordinal.{u}) (hd : delta ≤ alpha)
    (x : stage.model.RankElement (Order.succ delta)) :
    (stage.boundedRestrict ha k delta hd x).val = (k (stage.rankLift (Order.succ_le_succ hd) x)).val :=
  (stage.boundedRestrict_exists ha k delta hd).choose_spec x

end ModelStage
end IBLP
