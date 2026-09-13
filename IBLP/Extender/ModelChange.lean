import IBLP.Extender.Extension
import IBLP.Model.ElementaryCut

namespace IBLP.Extender.InternalExtension
open FullMarkedBLP Derivation
universe u
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}} {D : Derivation stage alpha beta}
  (E : InternalExtension D)

theorem ordinalImage_endpoint : stage.ordinalImage E.embedding alpha = beta := by
  change (E.embedding (stage.ordinal alpha)).val.rank = beta
  rw [E.endpoint, Ordinal.rank_toZFSet]

/-- The second identity of manuscript (5.1), for every internal set input. -/
theorem cut_embedding (z : stage.model.Element) :
    (E.next.cut beta (E.embedding z)).val = (stage.weakAction D.map z).val := by
  have h := stage.cut_image E.next E.embedding alpha z
  rw [E.ordinalImage_endpoint] at h
  have agreement := E.agreement (stage.rankCut alpha z)
  rw [stage.rankCut_include] at agreement
  exact (congrArg Subtype.val h).symm.trans agreement

theorem fixed_below_critical (c : Ordinal.{u}) (hc : c ≤ alpha)
    (critical : stage.model.GraphCriticalPoint D.graph (stage.ordinal c))
    (x : stage.model.Element) (below : x.val.rank < c) : (E.embedding x).val = x.val := by
  apply stage.fixed_below E.next E.embedding E.inside c ?_ x below
  intro rho hr
  change (E.embedding (stage.ordinal rho)).val.rank = rho
  rw [(E.critical_agrees c hc critical).2 rho hr, Ordinal.rank_toZFSet]

/-- No assertion that the critical ordinal itself is fixed is needed. -/
theorem cut_critical (c : Ordinal.{u}) (hc : c ≤ alpha)
    (critical : stage.model.GraphCriticalPoint D.graph (stage.ordinal c)) (z : stage.model.Element) :
    (E.next.cut c (E.embedding z)).val = (stage.cut c z).val := by
  apply ZFSet.ext
  intro x
  rw [E.next.cut_val, stage.cut_val, ZFSet.mem_inter, ZFSet.mem_inter, ZFSet.mem_vonNeumann]
  constructor
  · rintro ⟨hx, hr⟩
    have inside : x ∈ stage.model.carrier := E.inside (E.next.model.transitive hx (E.embedding z).property)
    have fixed := E.fixed_below_critical c hc critical ⟨x, inside⟩ hr
    exact ⟨(E.embedding.mem_iff ⟨x, inside⟩ z).mp (fixed.symm ▸ hx), hr⟩
  · rintro ⟨hx, hr⟩
    have inside := stage.model.transitive hx z.property
    have fixed := E.fixed_below_critical c hc critical ⟨x, inside⟩ hr
    have image := (E.embedding.mem_iff ⟨x, inside⟩ z).mpr hx
    change (E.embedding ⟨x, inside⟩).val ∈ (E.embedding z).val at image
    rw [fixed] at image
    exact ⟨image, hr⟩

end IBLP.Extender.InternalExtension
