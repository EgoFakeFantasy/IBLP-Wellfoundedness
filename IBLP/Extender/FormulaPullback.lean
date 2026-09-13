import IBLP.Extender.RepresentativeEquality

namespace IBLP.Extender
open FullMarkedBLP
universe u
namespace Derivation
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}

theorem formulaTest_pullback {n : Nat} (phi : RankPredicateFormula 0 n)
    (fs : Fin n → Representative stage alpha) (p : IndexMap stage alpha) :
    formulaTest phi (fun i => (fs i).pullback p) = preimage p (formulaTest phi fs) := by
  apply test_ext
  intro x
  rw [mem_formulaTest, preimage_val, ZFSet.mem_sep]
  simp only [Representative.pullback_value]
  constructor
  · intro h
    exact ⟨(stage.mem_hierarchy alpha x.val).mpr x.property,
      (Representative.indexValue p x).val, Representative.indexValue_edge p x,
      (mem_formulaTest phi fs (Representative.indexValue p x)).mpr h⟩
  · rintro ⟨_, y, edge, member⟩
    have same : y = (Representative.indexValue p x).val :=
      (p.function.2 x.val ((stage.mem_hierarchy alpha x.val).mpr x.property)).unique edge
        (Representative.indexValue_edge p x)
    rw [same] at member
    exact (mem_formulaTest phi fs (Representative.indexValue p x)).mp member

theorem holds_pullback_iff (D : Derivation stage alpha beta) (seed : Seed stage beta)
    {n : Nat} (phi : RankPredicateFormula 0 n) (fs : Fin n → Representative stage alpha) (p : IndexMap stage alpha) :
    D.Holds seed phi (fun i => (fs i).pullback p) ↔ D.Holds (D.project p seed) phi fs := by
  change D.Large seed _ ↔ _
  rw [formulaTest_pullback, D.large_preimage_iff]
  rfl

theorem repEquivalent_pullback_iff (D : Derivation stage alpha beta) (seed : Seed stage beta)
    (p : IndexMap stage alpha) (f g : Representative stage alpha) :
    D.RepEquivalent seed (f.pullback p) (g.pullback p) ↔ D.RepEquivalent (D.project p seed) f g := by
  have h := D.holds_pullback_iff seed (.equal 0 1) ![f, g] p
  have args : (fun i : Fin 2 => (![f, g] i).pullback p) = ![f.pullback p, g.pullback p] := by
    funext i; fin_cases i <;> rfl
  rw [args] at h
  exact h

end Derivation
end IBLP.Extender
