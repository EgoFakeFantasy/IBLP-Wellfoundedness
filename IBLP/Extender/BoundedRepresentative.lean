import IBLP.Extender.ConstantRepresentative

namespace IBLP.Extender
open FullMarkedBLP
universe u

/-- Actual internal function graphs with one prescribed set of possible values. -/
structure BoundedRepresentative (stage : ModelStage.{u}) (alpha : Ordinal.{u})
    (bound : stage.model.Element) where
  graph : stage.model.Element
  function : ZFSet.IsFunc (stage.hierarchy alpha).val bound.val graph.val

namespace BoundedRepresentative
variable {stage : ModelStage.{u}} {alpha : Ordinal.{u}} {bound : stage.model.Element}

def toRepresentative (f : BoundedRepresentative stage alpha bound) : Representative stage alpha :=
  ⟨bound, f.graph, f.function⟩

instance : Small.{u} (BoundedRepresentative stage alpha bound) := by
  let code : BoundedRepresentative stage alpha bound →
      (ZFSet.powerset (ZFSet.prod (stage.hierarchy alpha).val bound.val)) :=
    fun f => ⟨f.graph.val, ZFSet.mem_powerset.mpr f.function.1⟩
  apply small_of_injective (f := code)
  intro f g h
  have sameVal : f.graph.val = g.graph.val :=
    congrArg (fun z : (ZFSet.powerset (ZFSet.prod (stage.hierarchy alpha).val bound.val)) => z.val) h
  have same : f.graph = g.graph := Subtype.ext sameVal
  cases f
  cases g
  cases same
  rfl

end BoundedRepresentative

def representativeClipFormula : RankPredicateFormula 0 5 :=
  ((rankFormulaGraphApplies 0 3 4).and (.member 4 1)).or
    ((RankPredicateFormula.equal 4 2).and
      (RankPredicateFormula.ex ((rankFormulaGraphApplies 0 3 5).and (.member 5 1))).not)

namespace Representative
variable {stage : ModelStage.{u}} {alpha : Ordinal.{u}}

/-- Clipping is performed by an actual internal definable graph.
It preserves every value already in the specified bound. -/
theorem clip_exists (f : Representative stage alpha) (bound fallback : stage.model.Element)
    (inside : fallback.val ∈ bound.val) :
    ∃ g : BoundedRepresentative stage alpha bound, ∀ x : Derivation.Seed stage alpha,
      (f.value x).val ∈ bound.val → g.toRepresentative.value x = f.value x := by
  classical
  let values : Fin 3 → stage.model.Element := ![f.graph, bound, fallback]
  have sem (x : Derivation.Seed stage alpha) (y : stage.model.Element) :
      stage.model.realize representativeClipFormula (Fin.snoc (Fin.snoc values (stage.rankInclude _ x)) y) ↔
        y = if (f.value x).val ∈ bound.val then f.value x else fallback := by
    have base : stage.model.realize representativeClipFormula
        (Fin.snoc (Fin.snoc values (stage.rankInclude _ x)) y) ↔
        (ZFSet.pair x.val y.val ∈ f.graph.val ∧ y.val ∈ bound.val) ∨
          (y = fallback ∧ ¬∃ z : stage.model.Element, ZFSet.pair x.val z.val ∈ f.graph.val ∧ z.val ∈ bound.val) := by
      simp [representativeClipFormula, stage.model.realize_or, stage.model.realize_and,
        stage.model.realize_not, stage.model.realize_ex, stage.model.setGraphAtom_realize,
        TransitiveClass.realize, values, ModelStage.rankInclude]
    rw [base]
    simp only [f.edge_iff_value]
    by_cases h : (f.value x).val ∈ bound.val
    · simp only [h, if_true, exists_eq_left, not_true_eq_false, and_false, or_false]
      constructor
      · exact And.left
      · rintro rfl; exact ⟨rfl, h⟩
    · simp only [h, if_false, exists_eq_left, not_false_eq_true, and_true]
      exact or_iff_right (fun ⟨he, hm⟩ => False.elim (h (he ▸ hm)))
  obtain ⟨graph, function, edges⟩ := stage.definableGraph_exists representativeClipFormula values
    (stage.hierarchy alpha) bound
    (by
      intro x hx
      let a : Derivation.Seed stage alpha := ⟨x.val, (stage.mem_hierarchy alpha x.val).mp hx⟩
      exact ⟨_, (sem a _).mpr rfl⟩)
    (by
      intro x y hx hy
      let a : Derivation.Seed stage alpha := ⟨x.val, (stage.mem_hierarchy alpha x.val).mp hx⟩
      rw [(sem a y).mp hy]
      split_ifs with h
      · exact h
      · exact inside)
    (by
      intro x y z hx hy hz
      let a : Derivation.Seed stage alpha := ⟨x.val, (stage.mem_hierarchy alpha x.val).mp hx⟩
      exact ((sem a y).mp hy).trans ((sem a z).mp hz).symm)
  let g : BoundedRepresentative stage alpha bound := ⟨graph, function⟩
  refine ⟨g, fun x hx => ?_⟩
  have h := (sem x (g.toRepresentative.value x)).mp
    ((edges (stage.rankInclude _ x) (g.toRepresentative.value x)).mp (g.toRepresentative.value_edge x)).2
  simpa only [if_pos hx] using h

end Representative
end IBLP.Extender
