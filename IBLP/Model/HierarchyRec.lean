import IBLP.Model.Graph
import IBLP.Model.Powerset
import FullMarkedBLP.RankHierarchyRecursion

namespace IBLP
open FullMarkedBLP FirstOrder Language
universe u

namespace TransitiveClass

/-- The hierarchy recursion is interpreted in the model: only subsets belonging
to `M` are tested at each step. Existence of the graph is a separate obligation. -/
def HierarchyRec (M : TransitiveClass.{u}) (graph : M.Element) : Prop :=
  ∀ i value : M.Element, M.GraphApplies graph i value →
    ∀ z : M.Element, z.val ∈ value.val ↔
      ∃ a b : M.Element, a.val ∈ i.val ∧ M.GraphApplies graph a b ∧
        ∀ w : M.Element, w.val ∈ z.val → w.val ∈ b.val

theorem hierarchyRecFormula_realize (M : TransitiveClass.{u}) (graph : M.Element) :
    rankHierarchyRecFormula.Realize ![graph] ↔ M.HierarchyRec graph := by
  simp [rankHierarchyRecFormula, HierarchyRec, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_iff, BoundedFormula.realize_ex,
    BoundedFormula.realize_inf, M.memAt_realize, M.graphAppliesAt_realize, Fin.snoc]

theorem ElementaryMap.hierarchyRec_iff {M N : TransitiveClass.{u}} (j : M.ElementaryMap N)
    (graph : M.Element) : N.HierarchyRec (j graph) ↔ M.HierarchyRec graph := by
  have h := j.map_formula rankHierarchyRecFormula ![graph]
  have tuple : j ∘ ![graph] = ![j graph] := by funext i; fin_cases i; rfl
  rw [tuple, N.hierarchyRecFormula_realize, M.hierarchyRecFormula_realize] at h
  exact h

/-- An internal hierarchy value contains exactly the model's sets of smaller
ambient rank. The proof uses transitivity and the actual recursion graph only. -/
theorem hierarchyRec_mem_iff (M : TransitiveClass.{u})
    {graph domain range : M.Element}
    (function : M.IsFunction graph domain range) (ordinal : ZFSet.IsOrdinal domain.val)
    (recursion : M.HierarchyRec graph) (beta : Ordinal.{u}) :
    ∀ (level value : M.Element), level.val = beta.toZFSet → level.val ∈ domain.val →
      M.GraphApplies graph level value →
      ∀ z : ZFSet.{u}, z ∈ value.val ↔ z ∈ M.carrier ∧ z.rank < beta := by
  apply (wellFounded_lt : WellFounded ((· < ·) : Ordinal.{u} → Ordinal.{u} → Prop)).induction beta
  intro beta ih level value representation member applies z
  constructor
  · intro hz
    let z' := M.member value z hz
    obtain ⟨a, b, smaller, edge, subset⟩ := (recursion level value applies z').mp hz
    have smaller' : a.val ∈ beta.toZFSet := by simpa only [representation] using smaller
    obtain ⟨gamma, less, lowerRepresentation⟩ := Ordinal.mem_toZFSet_iff.mp smaller'
    have lowerMember : a.val ∈ domain.val := ordinal.mem_trans smaller member
    have lowerValue := ih gamma less a b lowerRepresentation.symm lowerMember edge
    refine ⟨z'.property, ZFSet.mem_vonNeumann.mp ?_⟩
    apply ZFSet.mem_vonNeumann'.mpr
    refine ⟨gamma, less, ?_⟩
    intro w hw
    have included := subset (M.member z' w hw) hw
    exact ZFSet.mem_vonNeumann.mpr ((lowerValue w).mp included).2
  · rintro ⟨modelMember, rankBound⟩
    let z' : M.Element := ⟨z, modelMember⟩
    obtain ⟨gamma, less, subset⟩ := ZFSet.mem_vonNeumann'.mp (ZFSet.mem_vonNeumann.mpr rankBound)
    have smaller : gamma.toZFSet ∈ level.val := by
      rw [representation]
      exact Ordinal.toZFSet_mem_toZFSet_iff.mpr less
    let lower := M.member level gamma.toZFSet smaller
    have lowerMember : lower.val ∈ domain.val := ordinal.mem_trans smaller member
    obtain ⟨b, _, edge, _⟩ := function.2 lower lowerMember
    have lowerValue := ih gamma less lower b rfl lowerMember edge
    apply (recursion level value applies z').mpr
    refine ⟨lower, b, smaller, edge, ?_⟩
    intro w hw
    exact (lowerValue w.val).mpr ⟨w.property, ZFSet.mem_vonNeumann.mp (subset hw)⟩

/-- The equality is an internal rank-section statement, not equality with the
whole ambient von Neumann level. -/
theorem hierarchyRec_value_unique (M : TransitiveClass.{u})
    {graph₁ domain₁ range₁ graph₂ domain₂ range₂ level₁ level₂ value₁ value₂ : M.Element}
    (function₁ : M.IsFunction graph₁ domain₁ range₁) (ordinal₁ : ZFSet.IsOrdinal domain₁.val)
    (recursion₁ : M.HierarchyRec graph₁)
    (function₂ : M.IsFunction graph₂ domain₂ range₂) (ordinal₂ : ZFSet.IsOrdinal domain₂.val)
    (recursion₂ : M.HierarchyRec graph₂) (beta : Ordinal.{u})
    (representation₁ : level₁.val = beta.toZFSet) (member₁ : level₁.val ∈ domain₁.val)
    (applies₁ : M.GraphApplies graph₁ level₁ value₁)
    (representation₂ : level₂.val = beta.toZFSet) (member₂ : level₂.val ∈ domain₂.val)
    (applies₂ : M.GraphApplies graph₂ level₂ value₂) : value₁ = value₂ := by
  apply Subtype.ext
  apply ZFSet.ext
  intro z
  rw [M.hierarchyRec_mem_iff function₁ ordinal₁ recursion₁ beta _ _ representation₁ member₁ applies₁,
    M.hierarchyRec_mem_iff function₂ ordinal₂ recursion₂ beta _ _ representation₂ member₂ applies₂]

theorem hierarchyRec_value_rank (M : TransitiveClass.{u})
    {graph domain range level value : M.Element}
    (function : M.IsFunction graph domain range) (ordinal : ZFSet.IsOrdinal domain.val)
    (recursion : M.HierarchyRec graph) (beta : Ordinal.{u})
    (representation : level.val = beta.toZFSet) (member : level.val ∈ domain.val)
    (applies : M.GraphApplies graph level value) : value.val.rank = beta := by
  have semantic := M.hierarchyRec_mem_iff function ordinal recursion beta level value
    representation member applies
  apply le_antisymm
  · exact ZFSet.rank_le_iff.mpr (fun _ hz => ((semantic _).mp hz).2)
  · have subset : beta.toZFSet ⊆ value.val := by
      intro z hz
      apply (semantic z).mpr
      refine ⟨M.transitive (by simpa only [representation] using hz) level.property, ?_⟩
      simpa only [Ordinal.rank_toZFSet] using ZFSet.rank_lt_of_mem hz
    simpa only [Ordinal.rank_toZFSet] using ZFSet.rank_mono subset

end TransitiveClass
end IBLP
