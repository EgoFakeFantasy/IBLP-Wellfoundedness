import IBLP.Model.GraphCriticalPoint
import IBLP.Model.PairCoordinate

namespace IBLP.TransitiveClass
open FullMarkedBLP
universe u

/-- The graph carries every quantified witness, so critical-point semantics
is absolute between transitive models containing the same graph and ordinal. -/
theorem graphCriticalPoint_external (M : IBLP.TransitiveClass.{u}) (g c : M.Element) :
    M.GraphCriticalPoint g c ↔ ZFSet.IsOrdinal c.val ∧
      (∃ y : ZFSet.{u}, ZFSet.pair c.val y ∈ g.val ∧ y ≠ c.val) ∧
      ∀ x : ZFSet.{u}, x ∈ c.val → ZFSet.pair x x ∈ g.val := by
  constructor
  · rintro ⟨ordinal, ⟨y, edge, moved⟩, fixed⟩
    refine ⟨ordinal, ⟨y.val, (M.graphApplies_absolute _ _ _).mp edge,
      fun same => moved (Subtype.ext same)⟩, ?_⟩
    intro x hx
    exact (M.graphApplies_absolute _ _ _).mp (fixed (M.member c x hx) hx)
  · rintro ⟨ordinal, ⟨y, edge, moved⟩, fixed⟩
    let y' : M.Element := ⟨y, (M.pair_components (M.transitive edge g.property)).2⟩
    refine ⟨ordinal, ⟨y', (M.graphApplies_absolute _ _ _).mpr edge,
      fun same => moved (congrArg Subtype.val same)⟩, ?_⟩
    exact fun x hx => (M.graphApplies_absolute _ _ _).mpr (fixed x.val hx)

theorem graphCriticalPoint_absolute (M N : IBLP.TransitiveClass.{u})
    (g c : M.Element) (g' c' : N.Element) (hg : g.val = g'.val) (hc : c.val = c'.val) :
    M.GraphCriticalPoint g c ↔ N.GraphCriticalPoint g' c' := by
  rw [M.graphCriticalPoint_external, N.graphCriticalPoint_external, hg, hc]

end IBLP.TransitiveClass
