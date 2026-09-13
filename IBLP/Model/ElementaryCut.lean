import IBLP.Model.InternalWeakAction
import IBLP.Model.SuccessorImage

namespace IBLP
open FullMarkedBLP
universe u
namespace ModelStage

theorem intersection_image (source target : ModelStage.{u})
    (j : source.model.ElementaryMap target.model) (x y : source.model.Element) :
    j (source.intersection x y) = target.intersection (j x) (j y) := by
  have h := j.map_formula rankIntersectionFormula ![source.intersection x y, x, y]
  have args : j ∘ ![source.intersection x y, x, y] = ![j (source.intersection x y), j x, j y] := by
    funext i; fin_cases i <;> rfl
  rw [args, target.model.intersectionFormula_realize, source.model.intersectionFormula_realize] at h
  exact Subtype.ext ((h.mpr (source.intersection_val x y)).trans (target.intersection_val (j x) (j y)).symm)

theorem cut_image (source target : ModelStage.{u})
    (j : source.model.ElementaryMap target.model) (rho : Ordinal.{u}) (z : source.model.Element) :
    j (source.cut rho z) = target.cut (source.ordinalImage j rho) (j z) := by
  unfold cut
  rw [source.intersection_image target j, source.hierarchy_image target j]

theorem rankCut_include (stage : ModelStage.{u}) (rho : Ordinal.{u}) (z : stage.model.Element) :
    stage.rankInclude (Order.succ rho) (stage.rankCut rho z) = stage.cut rho z := by
  apply Subtype.ext
  rw [show (stage.rankInclude (Order.succ rho) (stage.rankCut rho z)).val =
    (stage.rankCut rho z).val from rfl, stage.rankCut_val, stage.cut_val]

theorem image_rank_le (source target : ModelStage.{u})
    (j : source.model.ElementaryMap target.model) (x : source.model.Element) :
    (j x).val.rank ≤ source.ordinalImage j x.val.rank := by
  have inside : x.val ∈ (source.hierarchy (Order.succ x.val.rank)).val :=
    (source.mem_hierarchy_iff _ x).mpr (Order.lt_succ _)
  have image := (j.mem_iff x (source.hierarchy (Order.succ x.val.rank))).mpr inside
  rw [source.hierarchy_image target j, source.ordinalImage_succ, target.mem_hierarchy_iff] at image
  exact Order.lt_succ_iff.mp image

/-- Rank induction upgrades fixed ordinals to fixed sets. The target
inclusion is an explicit hypothesis here and is supplied by the extender proof. -/
theorem fixed_below (source target : ModelStage.{u}) (j : source.model.ElementaryMap target.model)
    (inside : target.model.carrier ⊆ source.model.carrier) (critical : Ordinal.{u})
    (fixed : ∀ rho < critical, source.ordinalImage j rho = rho)
    (x : source.model.Element) (below : x.val.rank < critical) : (j x).val = x.val := by
  have allSets : ∀ v : ZFSet.{u}, ∀ hv : v ∈ source.model.carrier, v.rank < critical →
      (j ⟨v, hv⟩).val = v := by
    intro v
    induction v using (InvImage.wf ZFSet.rank Ordinal.lt_wf).induction with
    | h v ih =>
      intro hv below
      let x : source.model.Element := ⟨v, hv⟩
      have bound : (j x).val.rank ≤ v.rank :=
        (source.image_rank_le target j x).trans_eq (fixed v.rank below)
      apply ZFSet.ext
      intro z
      constructor
      · intro hz
        have zm : z ∈ source.model.carrier := inside (target.model.transitive hz (j x).property)
        have zr : z.rank < v.rank := (ZFSet.rank_lt_of_mem hz).trans_le bound
        have ze : (j ⟨z, zm⟩).val = z := ih z zr zm (zr.trans below)
        exact (j.mem_iff ⟨z, zm⟩ x).mp (ze.symm ▸ hz)
      · intro hz
        have zm := source.model.transitive hz hv
        have ze := ih z (ZFSet.rank_lt_of_mem hz) zm ((ZFSet.rank_lt_of_mem hz).trans below)
        exact ze ▸ (j.mem_iff ⟨z, zm⟩ x).mpr hz
  exact allSets x.val x.property below

end ModelStage
end IBLP
