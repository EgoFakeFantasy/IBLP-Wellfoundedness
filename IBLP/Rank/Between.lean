import IBLP.Rank.Restriction
import FullMarkedBLP.RankIntersectionPreservation
import Mathlib.Tactic.FinCases

namespace IBLP
open FullMarkedBLP

universe u

abbrev RankMap (lambda mu : Ordinal.{u}) :=
  FirstOrder.Language.ElementaryEmbedding membershipLanguage (RankDomain lambda) (RankDomain mu)

theorem rankMap_mem_iff {lambda mu : Ordinal.{u}} (j : RankMap lambda mu)
    (x y : RankDomain lambda) : (j x).val ∈ (j y).val ↔ x.val ∈ y.val := by
  have h := j.map_rel (show membershipLanguage.Relations 2 from ⟨rfl⟩) ![x, y]
  simpa [FirstOrder.Language.Structure.RelMap, rankDomainMembershipStructure, Function.comp_def] using h

theorem rankMap_isOrdinal_iff {lambda mu : Ordinal.{u}} (j : RankMap lambda mu)
    (x : RankDomain lambda) : ZFSet.IsOrdinal (j x).val ↔ ZFSet.IsOrdinal x.val := by
  have h := j.map_formula rankOrdinalFormula ![x]
  have he : j ∘ ![x] = ![j x] := by funext i; fin_cases i; rfl
  rw [he, rankOrdinalFormula_realize, rankOrdinalFormula_realize] at h
  exact h

theorem rankMap_subset_iff {lambda mu : Ordinal.{u}} (j : RankMap lambda mu)
    (x y : RankDomain lambda) : (j x).val ⊆ (j y).val ↔ x.val ⊆ y.val := by
  have h := j.map_formula rankSubsetFormula ![x, y]
  have he : j ∘ ![x, y] = ![j x, j y] := by funext i; fin_cases i <;> rfl
  rw [he, rankSubsetFormula_realize, rankSubsetFormula_realize] at h
  exact h

theorem rankMap_intersection {lambda mu : Ordinal.{u}} (j : RankMap lambda mu)
    (x y : RankDomain lambda) : j (rankIntersection x y) = rankIntersection (j x) (j y) := by
  have h := j.map_formula rankIntersectionFormula ![rankIntersection x y, x, y]
  have he : j ∘ ![rankIntersection x y, x, y] = ![j (rankIntersection x y), j x, j y] := by
    funext i; fin_cases i <;> rfl
  rw [he, rankIntersectionFormula_realize, rankIntersectionFormula_realize] at h
  exact Subtype.ext (h.mpr rfl)

theorem rankMap_function_iff {lambda mu : Ordinal.{u}} (j : RankMap lambda mu)
    (f x y : RankDomain lambda) : rankIsFunction (j f) (j x) (j y) ↔ rankIsFunction f x y := by
  have h := j.map_formula rankFunctionFormula ![f, x, y]
  have he : j ∘ ![f, x, y] = ![j f, j x, j y] := by funext i; fin_cases i <;> rfl
  rw [he, rankFunctionFormula_realize, rankFunctionFormula_realize] at h
  exact h

theorem rankMap_hierarchyRec_iff {lambda mu : Ordinal.{u}} (j : RankMap lambda mu)
    (f : RankDomain lambda) : RankHierarchyRec (j f) ↔ RankHierarchyRec f := by
  have h := j.map_formula rankHierarchyRecFormula ![f]
  have he : j ∘ ![f] = ![j f] := by funext i; fin_cases i; rfl
  rw [he, rankHierarchyRecFormula_realize, rankHierarchyRecFormula_realize] at h
  exact h

noncomputable def ordinalAction {lambda mu : Ordinal.{u}} (j : RankMap lambda mu)
    (o : OrdinalDomain lambda) : OrdinalDomain mu :=
  ⟨(j (ordinalDomainElement o)).val.rank, (j (ordinalDomainElement o)).property⟩

theorem ordinalAction_compat {lambda mu : Ordinal.{u}} (j : RankMap lambda mu)
    (o : OrdinalDomain lambda) : (j (ordinalDomainElement o)).val = (ordinalAction j o).val.toZFSet :=
  ((rankMap_isOrdinal_iff j _).mpr (ZFSet.isOrdinal_toZFSet o.val)).toZFSet_rank_eq.symm

theorem ordinalAction_element {lambda mu : Ordinal.{u}} (j : RankMap lambda mu)
    (o : OrdinalDomain lambda) : ordinalDomainElement (ordinalAction j o) = j (ordinalDomainElement o) :=
  Subtype.ext (ordinalAction_compat j o).symm

theorem ordinalAction_lt_iff {lambda mu : Ordinal.{u}} (j : RankMap lambda mu)
    (a b : OrdinalDomain lambda) : ordinalAction j a < ordinalAction j b ↔ a < b := by
  change (ordinalAction j a).val < (ordinalAction j b).val ↔ a.val < b.val
  rw [← Ordinal.toZFSet_mem_toZFSet_iff, ← ordinalAction_compat j a, ← ordinalAction_compat j b]
  exact (rankMap_mem_iff j _ _).trans Ordinal.toZFSet_mem_toZFSet_iff

theorem ordinalAction_strictMono {lambda mu : Ordinal.{u}} (j : RankMap lambda mu) :
    StrictMono (ordinalAction j) := fun _ _ h => (ordinalAction_lt_iff j _ _).mpr h

theorem ordinalAction_inflationary {lambda mu : Ordinal.{u}} (j : RankMap lambda mu)
    (a : OrdinalDomain lambda) : a.val ≤ (ordinalAction j a).val := by
  induction a using (wellFounded_lt : WellFounded ((· < ·) : OrdinalDomain lambda → OrdinalDomain lambda → Prop)).induction with
  | h a ih =>
    by_contra hn
    have ha : (ordinalAction j a).val < a.val := lt_of_not_ge hn
    let b : OrdinalDomain lambda := ⟨(ordinalAction j a).val, ha.trans a.property⟩
    have lower : b < a := ha
    have hi := ih b lower
    have hd := (ordinalAction_strictMono j) lower
    exact (not_lt_of_ge hi) hd

end IBLP
