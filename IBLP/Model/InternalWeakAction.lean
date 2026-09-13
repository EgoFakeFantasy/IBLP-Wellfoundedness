import IBLP.Model.BoundedMap
import IBLP.Model.HierarchyAlgebra

namespace IBLP
open FullMarkedBLP
universe u

namespace ModelStage

/-- The canonical cut belongs to the full successor source rank, even when
its rank equals the source endpoint. -/
noncomputable def rankCut (stage : ModelStage.{u}) (alpha : Ordinal.{u})
    (z : stage.model.Element) : stage.model.RankElement (Order.succ alpha) :=
  ⟨(stage.cutSpace.cut alpha z).val, (stage.cutSpace.cut alpha z).property,
    Order.lt_succ_of_le (stage.cutSpace.cut_rank_le alpha z)⟩

theorem rankCut_val (stage : ModelStage.{u}) (alpha : Ordinal.{u})
    (z : stage.model.Element) : (stage.rankCut alpha z).val = z.val ∩ ZFSet.vonNeumann alpha := rfl

theorem rankCut_on_domain (stage : ModelStage.{u}) {alpha : Ordinal.{u}}
    (x : stage.model.RankElement (Order.succ alpha)) :
    stage.rankCut alpha (stage.rankInclude _ x) = x := by
  apply Subtype.ext
  have bound : stage.cutSpace.rank (stage.rankInclude _ x) ≤ alpha :=
    Order.lt_succ_iff.mp x.property.2
  exact congrArg (fun z : stage.model.Element => z.val) (stage.cutSpace.cut_eq_self bound)

/-- Manuscript (3.5), on every actual element of the current internal model. -/
noncomputable def weakAction (stage : ModelStage.{u}) {alpha beta : Ordinal.{u}}
    (k : stage.BoundedMap alpha beta) (z : stage.model.Element) : stage.model.Element :=
  stage.rankInclude _ (k (stage.rankCut alpha z))

theorem weakAction_rank_le (stage : ModelStage.{u}) {alpha beta : Ordinal.{u}}
    (k : stage.BoundedMap alpha beta) (z : stage.model.Element) :
    (stage.weakAction k z).val.rank ≤ beta :=
  Order.lt_succ_iff.mp (k (stage.rankCut alpha z)).property.2

theorem weakAction_on_domain (stage : ModelStage.{u}) {alpha beta : Ordinal.{u}}
    (k : stage.BoundedMap alpha beta) (x : stage.model.RankElement (Order.succ alpha)) :
    stage.weakAction k (stage.rankInclude _ x) = stage.rankInclude _ (k x) := by
  unfold weakAction
  rw [stage.rankCut_on_domain]

theorem rankCut_cut (stage : ModelStage.{u}) {alpha gamma : Ordinal.{u}}
    (h : alpha ≤ gamma) (z : stage.model.Element) :
    stage.rankCut alpha (stage.cutSpace.cut gamma z) = stage.rankCut alpha z := by
  apply Subtype.ext
  exact congrArg (fun w : stage.model.Element => w.val) (stage.cutSpace.cut_lower h z)

theorem weakAction_cut (stage : ModelStage.{u}) {alpha beta gamma : Ordinal.{u}}
    (k : stage.BoundedMap alpha beta) (h : alpha ≤ gamma) (z : stage.model.Element) :
    stage.weakAction k (stage.cutSpace.cut gamma z) = stage.weakAction k z := by
  unfold weakAction
  rw [stage.rankCut_cut h]

noncomputable def rankIntersection (stage : ModelStage.{u}) {lambda : Ordinal.{u}}
    (x y : stage.model.RankElement lambda) : stage.model.RankElement lambda :=
  ⟨(stage.intersection (stage.rankInclude _ x) (stage.rankInclude _ y)).val,
    (stage.intersection (stage.rankInclude _ x) (stage.rankInclude _ y)).property, by
      rw [stage.intersection_val]
      exact (ZFSet.rank_mono (fun _ h => (ZFSet.mem_inter.mp h).1)).trans_lt x.property.2⟩

theorem rankIntersection_val (stage : ModelStage.{u}) {lambda : Ordinal.{u}}
    (x y : stage.model.RankElement lambda) :
    (stage.rankIntersection x y).val = x.val ∩ y.val := stage.intersection_val _ _

theorem rankMap_intersection (stage : ModelStage.{u}) {lambda mu : Ordinal.{u}}
    (k : (stage.model.rankPart lambda).ElementaryMap (stage.model.rankPart mu))
    (x y : stage.model.RankElement lambda) :
    k (stage.rankIntersection x y) = stage.rankIntersection (k x) (k y) := by
  have h := k.map_formula rankIntersectionFormula ![stage.rankIntersection x y, x, y]
  have tuple : k ∘ ![stage.rankIntersection x y, x, y] =
      ![k (stage.rankIntersection x y), k x, k y] := by
    funext i
    fin_cases i <;> rfl
  rw [tuple, (stage.model.rankPart mu).intersectionFormula_realize,
    (stage.model.rankPart lambda).intersectionFormula_realize] at h
  apply Subtype.ext
  exact (h.mpr (stage.rankIntersection_val x y)).trans (stage.rankIntersection_val (k x) (k y)).symm

end ModelStage
end IBLP
