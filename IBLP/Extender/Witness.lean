import IBLP.Extender.FormulaTest
import IBLP.Model.GraphWitness

namespace IBLP.Extender
open FullMarkedBLP
universe u
namespace Derivation
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}

theorem graphWitness_values {n : Nat} (phi : RankPredicateFormula 0 (n + 1))
    (fs : Fin n → Representative stage alpha) (x : Seed stage alpha) (y : stage.model.Element) :
    stage.model.realize (graphWitness phi)
      (Fin.snoc (Fin.snoc (fun i => (fs i).graph) (stage.rankInclude _ x)) y) ↔
      stage.model.realize phi (Fin.snoc (fun i => (fs i).value x) y) := by
  rw [graphWitness_realize]
  constructor
  · rintro ⟨values, edges, h⟩
    have same : values = fun i => (fs i).value x := funext (fun i => (fs i).value_unique x _ (edges i))
    simpa only [same] using h
  · intro h
    exact ⟨fun i => (fs i).value x, fun i => (fs i).value_edge x, h⟩

theorem witness_exists {n : Nat} (phi : RankPredicateFormula 0 (n + 1))
    (fs : Fin n → Representative stage alpha) :
    ∃ f : Representative stage alpha, ∀ x : Seed stage alpha,
      (∃ y : stage.model.Element, stage.model.realize phi (Fin.snoc (fun i => (fs i).value x) y)) →
        stage.model.realize phi (Fin.snoc (fun i => (fs i).value x) (f.value x)) := by
  classical
  have total (x : stage.model.Element) (_ : x.val ∈ (stage.hierarchy alpha).val) :
      ∃ y : stage.model.Element, stage.model.realize (graphWitnessChoice phi)
        (Fin.snoc (Fin.snoc (fun i => (fs i).graph) x) y) := by
    by_cases h : ∃ y : stage.model.Element, stage.model.realize (graphWitness phi)
        (Fin.snoc (Fin.snoc (fun i => (fs i).graph) x) y)
    · obtain ⟨y, hy⟩ := h
      exact ⟨y, (graphWitnessChoice_realize _ _ _ _ _).mpr (fun _ => hy)⟩
    · exact ⟨stage.ordinal 0, (graphWitnessChoice_realize _ _ _ _ _).mpr (fun ht => False.elim (h ht))⟩
  let chosen := stage.choiceFunction (graphWitnessChoice phi) (fun i => (fs i).graph) (stage.hierarchy alpha) total
  let f : Representative stage alpha := ⟨chosen.range, chosen.graph, chosen.isFunction⟩
  refine ⟨f, fun x hx => ?_⟩
  have spec := chosen.satisfies (stage.rankInclude _ x) (f.value x) (f.value_edge x)
  apply (graphWitness_values phi fs x (f.value x)).mp
  apply (graphWitnessChoice_realize _ _ _ _ _).mp spec
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, (graphWitness_values phi fs x y).mpr hy⟩

theorem holds_ex_iff (D : Derivation stage alpha beta) (seed : Seed stage beta) {n : Nat}
    (phi : RankPredicateFormula 0 (n + 1)) (fs : Fin n → Representative stage alpha) :
    D.Holds seed phi.ex fs ↔ ∃ f : Representative stage alpha, D.Holds seed phi (Fin.snoc fs f) := by
  constructor
  · intro h
    obtain ⟨f, hf⟩ := witness_exists phi fs
    refine ⟨f, D.holds_mono seed phi.ex phi fs (Fin.snoc fs f) (fun x hx => ?_) h⟩
    have values : (fun i : Fin (n + 1) => Representative.value
        (Fin.snoc (α := fun _ => Representative stage alpha) fs f i) x) =
        Fin.snoc (fun i => (fs i).value x) (f.value x) := by
      funext i
      cases i using Fin.lastCases with
      | last => simp
      | cast i => simp
    rw [values]
    exact hf x ((stage.model.realize_ex _ _).mp hx)
  · rintro ⟨f, hf⟩
    apply D.holds_mono seed phi phi.ex (Fin.snoc fs f) fs (fun x hx => ?_) hf
    apply (stage.model.realize_ex _ _).mpr
    refine ⟨f.value x, ?_⟩
    have values : (fun i : Fin (n + 1) => Representative.value
        (Fin.snoc (α := fun _ => Representative stage alpha) fs f i) x) =
        Fin.snoc (fun i => (fs i).value x) (f.value x) := by
      funext i
      cases i using Fin.lastCases with
      | last => simp
      | cast i => simp
    rwa [← values]

theorem holds_all_iff (D : Derivation stage alpha beta) (seed : Seed stage beta) {n : Nat}
    (phi : RankPredicateFormula 0 (n + 1)) (fs : Fin n → Representative stage alpha) :
    D.Holds seed (.all phi) fs ↔ ∀ f : Representative stage alpha, D.Holds seed phi (Fin.snoc fs f) := by
  classical
  have equivalent := D.holds_congr seed (.all phi) phi.not.ex.not fs fs (fun x => by
    simp only [stage.model.realize_not, stage.model.realize_ex, TransitiveClass.realize, not_exists, not_not])
  rw [equivalent, D.holds_not_iff, D.holds_ex_iff]
  simp only [D.holds_not_iff, not_exists, not_not]

end Derivation
end IBLP.Extender
