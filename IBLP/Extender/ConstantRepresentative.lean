import IBLP.Extender.FormulaTest

namespace IBLP.Extender
open FullMarkedBLP
universe u
namespace Representative
variable {stage : ModelStage.{u}} {alpha : Ordinal.{u}}

theorem constant_exists (y : stage.model.Element) :
    ∃ f : Representative stage alpha, ∀ x : Derivation.Seed stage alpha, f.value x = y := by
  let phi : RankPredicateFormula 0 3 := .equal 2 0
  have sem (x z : stage.model.Element) :
      stage.model.realize phi (Fin.snoc (Fin.snoc ![y] x) z) ↔ z = y := Iff.rfl
  obtain ⟨graph, function, edges⟩ := stage.definableGraph_exists phi ![y]
    (stage.hierarchy alpha) (stage.unorderedPair y y)
    (fun x _ => ⟨y, (sem x y).mpr rfl⟩)
    (by intro x z _ h; rw [(sem x z).mp h, stage.unorderedPair_val]; simp)
    (fun x z w _ hz hw => ((sem x z).mp hz).trans ((sem x w).mp hw).symm)
  let f : Representative stage alpha := ⟨stage.unorderedPair y y, graph, function⟩
  refine ⟨f, fun x => ?_⟩
  exact (sem (stage.rankInclude _ x) (f.value x)).mp
    ((edges (stage.rankInclude _ x) (f.value x)).mp (f.value_edge x)).2

noncomputable def constant (y : stage.model.Element) : Representative stage alpha := (constant_exists y).choose

theorem constant_value (y : stage.model.Element) (x : Derivation.Seed stage alpha) :
    (constant y).value x = y := (constant_exists y).choose_spec x

end Representative
namespace Derivation
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}

theorem holds_of_pointwise (D : Derivation stage alpha beta) (seed : Seed stage beta) {n : Nat}
    (phi : RankPredicateFormula 0 n) (fs : Fin n → Representative stage alpha)
    (h : ∀ x : Seed stage alpha, stage.model.realize phi (fun i => (fs i).value x)) : D.Holds seed phi fs := by
  have same : formulaTest phi fs = top := test_ext (fun x => by
    rw [mem_formulaTest]
    exact iff_of_true (h x) ((stage.mem_hierarchy alpha x.val).mpr x.property))
  change D.Large seed _
  rw [same]
  exact D.large_top seed

theorem holds_constant_iff (D : Derivation stage alpha beta) (seed : Seed stage beta) {n : Nat}
    (phi : RankPredicateFormula 0 n) (values : Fin n → stage.model.Element) :
    D.Holds seed phi (Representative.constant ∘ values) ↔ stage.model.realize phi values := by
  classical
  have pointwise (x : Seed stage alpha) :
      (fun i => ((Representative.constant ∘ values) i).value x) = values := by
    funext i
    exact Representative.constant_value (values i) x
  constructor
  · intro h
    by_contra hfalse
    have neg := D.holds_of_pointwise seed phi.not (Representative.constant ∘ values) (fun x => by
      rw [stage.model.realize_not, pointwise]
      exact hfalse)
    exact ((D.holds_not_iff seed phi _).mp neg) h
  · intro h
    exact D.holds_of_pointwise seed phi _ (fun x => by rw [pointwise]; exact h)

end Derivation
end IBLP.Extender
