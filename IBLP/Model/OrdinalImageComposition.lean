import IBLP.Model.HierarchyImage

namespace IBLP.ModelStage
open FullMarkedBLP
universe u

theorem ordinalImage_refl (stage : ModelStage.{u}) (eta : Ordinal.{u}) :
    stage.ordinalImage (FirstOrder.Language.ElementaryEmbedding.refl membershipLanguage stage.model.Element) eta = eta :=
  Ordinal.rank_toZFSet eta

theorem ordinalImage_comp (M N P : ModelStage.{u})
    (j : M.model.ElementaryMap N.model) (k : N.model.ElementaryMap P.model) (eta : Ordinal.{u}) :
    M.ordinalImage (k.comp j) eta = N.ordinalImage k (M.ordinalImage j eta) := by
  have image : j (M.ordinal eta) = N.ordinal (M.ordinalImage j eta) := Subtype.ext (M.ordinalImage_compat j eta)
  change (k (j (M.ordinal eta))).val.rank = (k (N.ordinal (M.ordinalImage j eta))).val.rank
  rw [image]

end IBLP.ModelStage
