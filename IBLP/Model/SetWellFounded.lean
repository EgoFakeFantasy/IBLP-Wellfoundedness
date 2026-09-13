import IBLP.Model.GraphEqualizer
import IBLP.Model.Powerset
import Mathlib.Order.WellFounded

namespace IBLP
open FullMarkedBLP
universe u

instance setDomain_small (domain : ZFSet.{u}) : Small.{u} (SetDomain domain) := ZFSet.small_coe domain

def setWellFoundedMatrix : RankPredicateFormula 0 2 :=
  .all (((rankPredicateAtom rankSubsetFormula ![2, 0]).and
    ((RankPredicateFormula.member 3 2).ex)).imp
      (((RankPredicateFormula.member 3 2).and
        (.all ((RankPredicateFormula.member 4 2).imp (rankFormulaGraphApplies 1 4 3).not))).ex))

theorem setWellFoundedMatrix_realize (M : TransitiveClass.{u}) (domain relation : M.Element) :
    M.realize setWellFoundedMatrix ![domain, relation] ↔
      ∀ s : M.Element, s.val ⊆ domain.val → (∃ x : M.Element, x.val ∈ s.val) →
        ∃ m : M.Element, m.val ∈ s.val ∧
          ∀ x : M.Element, x.val ∈ s.val → ZFSet.pair x.val m.val ∉ relation.val := by
  have subsetSem (s : M.Element) : M.realize (rankPredicateAtom rankSubsetFormula ![2, 0])
      ![domain, relation, s] ↔ s.val ⊆ domain.val := by
    rw [M.realize_atom]
    have args : ![domain, relation, s] ∘ ![2, 0] = ![s, domain] := by
      funext i; fin_cases i <;> rfl
    rw [args, M.subsetFormula_realize]
  change (∀ s, _ → _) ↔ _
  simp [M.realize_and, subsetSem, M.realize_ex, M.realize_not,
    TransitiveClass.realize, M.setGraphAtom_realize, and_imp]

def setRelation (domain relation : ZFSet.{u}) (x y : SetDomain domain) : Prop :=
  ZFSet.pair x.val y.val ∈ relation

/-- External well-foundedness always implies the finite internal
well-foundedness assertion in a transitive class. -/
theorem setWellFounded_of_external (M : TransitiveClass.{u}) (domain relation : M.Element)
    (wf : WellFounded (setRelation domain.val relation.val)) :
    M.realize setWellFoundedMatrix ![domain, relation] := by
  apply (setWellFoundedMatrix_realize M domain relation).mpr
  intro s subset ⟨x, hx⟩
  let S : Set (SetDomain domain.val) := {z | z.val ∈ s.val}
  obtain ⟨m, hm, minimal⟩ := wf.has_min S ⟨⟨x.val, subset hx⟩, hx⟩
  refine ⟨M.member s m.val hm, hm, ?_⟩
  intro y hy
  exact minimal ⟨y.val, subset hy⟩ hy

/-- In the full ambient universe, the finite formula tests all subsets
and therefore implies actual well-foundedness. -/
theorem universe_setWellFounded_iff (domain relation : universeClass.{u}.toTransitiveClass.Element) :
    universeClass.toTransitiveClass.realize setWellFoundedMatrix ![domain, relation] ↔
      WellFounded (setRelation domain.val relation.val) := by
  constructor
  · intro h
    have sem := (setWellFoundedMatrix_realize _ _ _).mp h
    apply WellFounded.wellFounded_iff_has_min.mpr
    intro S ⟨a, ha⟩
    let s : universeClass.{u}.toTransitiveClass.Element :=
      ⟨ZFSet.sep (fun z => ∃ hz : z ∈ domain.val, (⟨z, hz⟩ : SetDomain domain.val) ∈ S) domain.val, Set.mem_univ _⟩
    have mem_s (z : ZFSet.{u}) : z ∈ s.val ↔ z ∈ domain.val ∧
        ∃ hz : z ∈ domain.val, (⟨z, hz⟩ : SetDomain domain.val) ∈ S := by
      dsimp only [s]
      rw [ZFSet.mem_sep]
    have subset : s.val ⊆ domain.val := by intro z hz; exact ((mem_s z).mp hz).1
    have nonempty : ∃ x : universeClass.{u}.toTransitiveClass.Element, x.val ∈ s.val := by
      refine ⟨⟨a.val, Set.mem_univ _⟩, ?_⟩
      exact (mem_s a.val).mpr ⟨a.property, a.property, ha⟩
    obtain ⟨m, hm, minimal⟩ := sem s subset nonempty
    obtain ⟨hmDomain, hmS⟩ := (mem_s m.val).mp hm
    obtain ⟨hmDomain', hmS⟩ := hmS
    refine ⟨⟨m.val, hmDomain⟩, hmS, ?_⟩
    intro x hx
    exact minimal ⟨x.val, Set.mem_univ _⟩ ((mem_s x.val).mpr ⟨x.property, x.property, hx⟩)
  · exact setWellFounded_of_external _ _ _

end IBLP
