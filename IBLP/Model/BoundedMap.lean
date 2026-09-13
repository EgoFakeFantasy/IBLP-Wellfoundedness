import IBLP.Model.RankBridge
import IBLP.Model.HierarchyAlgebra

namespace IBLP
open FullMarkedBLP
universe u

namespace ModelStage

/-- An elementary map between the actual successor rank cuts of one internal
model. It need not be the restriction of any global elementary map. -/
abbrev BoundedMap (stage : ModelStage.{u}) (alpha beta : Ordinal.{u}) :=
  (stage.model.rankPart (Order.succ alpha)).ElementaryMap
    (stage.model.rankPart (Order.succ beta))

noncomputable def rankOrdinal (stage : ModelStage.{u}) {lambda : Ordinal.{u}}
    (o : OrdinalDomain lambda) : stage.model.RankElement lambda :=
  ⟨o.val.toZFSet, stage.ordinalComplete o.val, by simpa only [Ordinal.rank_toZFSet] using o.property⟩

noncomputable def rankHierarchy (stage : ModelStage.{u}) {lambda : Ordinal.{u}}
    (o : OrdinalDomain lambda) : stage.model.RankElement lambda :=
  ⟨(stage.hierarchy o.val).val, (stage.hierarchy o.val).property,
    by simpa only [stage.hierarchy_rank] using o.property⟩

@[simp] theorem rankOrdinal_val (stage : ModelStage.{u}) {lambda : Ordinal.{u}}
    (o : OrdinalDomain lambda) : (stage.rankOrdinal o).val = o.val.toZFSet := rfl

@[simp] theorem rankHierarchy_val (stage : ModelStage.{u}) {lambda : Ordinal.{u}}
    (o : OrdinalDomain lambda) : (stage.rankHierarchy o).val = (stage.hierarchy o.val).val := rfl

noncomputable def rankOrdinalAction (stage : ModelStage.{u}) {lambda mu : Ordinal.{u}}
    (j : (stage.model.rankPart lambda).ElementaryMap (stage.model.rankPart mu))
    (o : OrdinalDomain lambda) : OrdinalDomain mu :=
  ⟨(j (stage.rankOrdinal o)).val.rank, (j (stage.rankOrdinal o)).property.2⟩

theorem rankOrdinalAction_compat (stage : ModelStage.{u}) {lambda mu : Ordinal.{u}}
    (j : (stage.model.rankPart lambda).ElementaryMap (stage.model.rankPart mu))
    (o : OrdinalDomain lambda) :
    (j (stage.rankOrdinal o)).val = (stage.rankOrdinalAction j o).val.toZFSet :=
  ((j.isOrdinal_iff _).mpr (ZFSet.isOrdinal_toZFSet o.val)).toZFSet_rank_eq.symm

theorem rankOrdinalAction_element (stage : ModelStage.{u}) {lambda mu : Ordinal.{u}}
    (j : (stage.model.rankPart lambda).ElementaryMap (stage.model.rankPart mu))
    (o : OrdinalDomain lambda) :
    stage.rankOrdinal (stage.rankOrdinalAction j o) = j (stage.rankOrdinal o) :=
  Subtype.ext (stage.rankOrdinalAction_compat j o).symm

theorem rankOrdinalAction_lt_iff (stage : ModelStage.{u}) {lambda mu : Ordinal.{u}}
    (j : (stage.model.rankPart lambda).ElementaryMap (stage.model.rankPart mu))
    (a b : OrdinalDomain lambda) :
    stage.rankOrdinalAction j a < stage.rankOrdinalAction j b ↔ a < b := by
  change (stage.rankOrdinalAction j a).val < (stage.rankOrdinalAction j b).val ↔ a.val < b.val
  rw [← Ordinal.toZFSet_mem_toZFSet_iff, ← stage.rankOrdinalAction_compat j a,
    ← stage.rankOrdinalAction_compat j b]
  exact (j.mem_iff _ _).trans Ordinal.toZFSet_mem_toZFSet_iff

theorem rankOrdinalAction_strictMono (stage : ModelStage.{u}) {lambda mu : Ordinal.{u}}
    (j : (stage.model.rankPart lambda).ElementaryMap (stage.model.rankPart mu)) :
    StrictMono (stage.rankOrdinalAction j) := fun _ _ h => (stage.rankOrdinalAction_lt_iff j _ _).mpr h

theorem rankOrdinalAction_inflationary (stage : ModelStage.{u}) {lambda mu : Ordinal.{u}}
    (j : (stage.model.rankPart lambda).ElementaryMap (stage.model.rankPart mu))
    (a : OrdinalDomain lambda) : a.val ≤ (stage.rankOrdinalAction j a).val := by
  induction a using (wellFounded_lt : WellFounded
    ((· < ·) : OrdinalDomain lambda → OrdinalDomain lambda → Prop)).induction with
  | h a ih =>
    by_contra hn
    have ha : (stage.rankOrdinalAction j a).val < a.val := lt_of_not_ge hn
    let b : OrdinalDomain lambda := ⟨(stage.rankOrdinalAction j a).val, ha.trans a.property⟩
    have lower : b < a := ha
    have hi := ih b lower
    have hd := (stage.rankOrdinalAction_strictMono j) lower
    exact (not_lt_of_ge hi) hd

end ModelStage
end IBLP
