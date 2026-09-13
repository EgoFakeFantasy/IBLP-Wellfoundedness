import IBLP.Model.WeakActionImage
import IBLP.Model.InternalWeakTruncation
import IBLP.Model.Inaccessible
import IBLP.Rank.WordImage

namespace IBLP.ModelStage
open FullMarkedBLP
universe u

theorem ordinalImage_isSuccLimit (source target : ModelStage.{u})
    (j : source.model.ElementaryMap target.model) (rho : Ordinal.{u}) (limit : Order.IsSuccLimit rho) :
    Order.IsSuccLimit (source.ordinalImage j rho) := by
  have h := j.map_formula rankNonzeroLimitFormula ![source.ordinal rho]
  have args : j ∘ ![source.ordinal rho] = ![j (source.ordinal rho)] := by
    funext i; fin_cases i; rfl
  rw [args, target.model.nonzeroLimitFormula_absolute, source.model.nonzeroLimitFormula_absolute,
    source.ordinalImage_compat] at h
  exact (setNonzeroLimit_ordinal_iff _).mp (h.mpr ((setNonzeroLimit_ordinal_iff rho).mpr limit))

theorem rho_image (source target : ModelStage.{u})
    (j : source.model.ElementaryMap target.model) (rho sigma : Ordinal.{u})
    (graph : source.model.Element) (elementary : source.InternalGraphElementary rho sigma graph)
    (eta : Ordinal.{u}) :
    target.rho ((source.internalGraphElementary_image target j rho sigma graph).mpr elementary).toRankEmbedding
      (source.ordinalImage j eta) = source.ordinalImage j (source.rho elementary.toRankEmbedding eta) := by
  have h := source.weakAction_image target j rho sigma graph elementary (source.ordinal eta)
  have ordinalEq : j (source.ordinal eta) = target.ordinal (source.ordinalImage j eta) :=
    Subtype.ext (source.ordinalImage_compat j eta)
  rw [ordinalEq, target.weakAction_ordinal, source.weakAction_ordinal] at h
  have values := congrArg Subtype.val h
  rw [source.ordinalImage_compat] at values
  exact Ordinal.toZFSet_injective values

/-- The abstract word-image fields are all discharged for actual saved
graphs. Arbitrary finite products now follow from CutAction.Image.word. -/
theorem boundedCutAction_image (source target : ModelStage.{u})
    (j : source.model.ElementaryMap target.model) (rho sigma : Ordinal.{u})
    (limit : Order.IsSuccLimit rho) (graph : source.model.Element)
    (elementary : source.InternalGraphElementary rho sigma graph) :
    CutAction.Image j (source.ordinalImage j)
      (source.boundedCutAction limit elementary.toRankEmbedding)
      (target.boundedCutAction (source.ordinalImage_isSuccLimit target j rho limit)
        ((source.internalGraphElementary_image target j rho sigma graph).mpr elementary).toRankEmbedding) where
  act := source.weakAction_image target j rho sigma graph elementary
  rho := source.rho_image target j rho sigma graph elementary
  bound := rfl

end IBLP.ModelStage
