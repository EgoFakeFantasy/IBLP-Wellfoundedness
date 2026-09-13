import IBLP.Extender.Representative
import IBLP.Model.GraphEvaluation

namespace IBLP.Extender
open FullMarkedBLP
universe u
namespace Derivation
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}

theorem test_ext {x y : Test stage alpha}
    (h : ∀ z : Seed stage alpha, z.val ∈ x.val ↔ z.val ∈ y.val) : x = y := by
  apply Subtype.ext
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    let a : Seed stage alpha := ⟨z, (stage.mem_hierarchy alpha z).mp (test_subset x hz)⟩
    exact (h a).mp hz
  · intro hz
    let a : Seed stage alpha := ⟨z, (stage.mem_hierarchy alpha z).mp (test_subset y hz)⟩
    exact (h a).mpr hz

theorem test_subset_of_pointwise {x y : Test stage alpha}
    (h : ∀ z : Seed stage alpha, z.val ∈ x.val → z.val ∈ y.val) : x.val ⊆ y.val := by
  intro z hz
  exact h ⟨z, (stage.mem_hierarchy alpha z).mp (test_subset x hz)⟩ hz

noncomputable def formulaTest {n : Nat} (phi : RankPredicateFormula 0 n)
    (fs : Fin n → Representative stage alpha) : Test stage alpha :=
  let result := stage.separation (graphEvaluation phi) (fun i => (fs i).graph) (stage.hierarchy alpha)
  subsetTest top result (by
    intro z hz
    exact ((stage.mem_separation _ _ _ (stage.model.member result z hz)).mp hz).1)

theorem mem_formulaTest {n : Nat} (phi : RankPredicateFormula 0 n)
    (fs : Fin n → Representative stage alpha) (x : Seed stage alpha) :
    x.val ∈ (formulaTest phi fs).val ↔ stage.model.realize phi (fun i => (fs i).value x) := by
  change (stage.rankInclude _ x).val ∈ (stage.separation (graphEvaluation phi)
    (fun i => (fs i).graph) (stage.hierarchy alpha)).val ↔ _
  rw [stage.mem_separation, graphEvaluation_realize]
  constructor
  · rintro ⟨_, values, edges, h⟩
    have same : values = fun i => (fs i).value x := funext (fun i => (fs i).value_unique x _ (edges i))
    simpa only [same] using h
  · intro h
    exact ⟨(stage.mem_hierarchy alpha x.val).mpr x.property, fun i => (fs i).value x,
      fun i => (fs i).value_edge x, h⟩

def Holds (D : Derivation stage alpha beta) (seed : Seed stage beta) {n : Nat}
    (phi : RankPredicateFormula 0 n) (fs : Fin n → Representative stage alpha) : Prop :=
  D.Large seed (formulaTest phi fs)

theorem holds_congr (D : Derivation stage alpha beta) (seed : Seed stage beta) {n m : Nat}
    (phi : RankPredicateFormula 0 n) (psi : RankPredicateFormula 0 m)
    (fs : Fin n → Representative stage alpha) (gs : Fin m → Representative stage alpha)
    (h : ∀ x : Seed stage alpha, stage.model.realize phi (fun i => (fs i).value x) ↔
      stage.model.realize psi (fun i => (gs i).value x)) : D.Holds seed phi fs ↔ D.Holds seed psi gs := by
  have same : formulaTest phi fs = formulaTest psi gs := test_ext (fun x => by
    rw [mem_formulaTest, mem_formulaTest]; exact h x)
  change D.Large seed _ ↔ D.Large seed _
  rw [same]

theorem holds_mono (D : Derivation stage alpha beta) (seed : Seed stage beta) {n m : Nat}
    (phi : RankPredicateFormula 0 n) (psi : RankPredicateFormula 0 m)
    (fs : Fin n → Representative stage alpha) (gs : Fin m → Representative stage alpha)
    (h : ∀ x : Seed stage alpha, stage.model.realize phi (fun i => (fs i).value x) →
      stage.model.realize psi (fun i => (gs i).value x)) : D.Holds seed phi fs → D.Holds seed psi gs :=
  D.large_mono seed (test_subset_of_pointwise (fun x hx =>
    (mem_formulaTest psi gs x).mpr (h x ((mem_formulaTest phi fs x).mp hx))))

theorem formulaTest_falsum {n : Nat} (fs : Fin n → Representative stage alpha) :
    formulaTest (.falsum : RankPredicateFormula 0 n) fs = bottom := by
  apply test_ext
  intro x
  rw [mem_formulaTest]
  simp [TransitiveClass.realize, bottom]

theorem not_holds_falsum (D : Derivation stage alpha beta) (seed : Seed stage beta) {n : Nat}
    (fs : Fin n → Representative stage alpha) : ¬D.Holds seed .falsum fs := by
  change ¬D.Large seed _
  rw [formulaTest_falsum]
  exact D.not_large_bottom seed

theorem formulaTest_not {n : Nat} (phi : RankPredicateFormula 0 n) (fs : Fin n → Representative stage alpha) :
    formulaTest phi.not fs = compl (formulaTest phi fs) := by
  apply test_ext
  intro x
  rw [mem_formulaTest, compl_val, ZFSet.mem_sep, mem_formulaTest]
  exact (stage.model.realize_not phi _).trans
    (and_iff_right ((stage.mem_hierarchy alpha x.val).mpr x.property)).symm

theorem holds_not_iff (D : Derivation stage alpha beta) (seed : Seed stage beta) {n : Nat}
    (phi : RankPredicateFormula 0 n) (fs : Fin n → Representative stage alpha) :
    D.Holds seed phi.not fs ↔ ¬D.Holds seed phi fs := by
  change D.Large seed _ ↔ _
  rw [formulaTest_not, D.large_compl_iff]
  rfl

theorem formulaTest_and {n : Nat} (phi psi : RankPredicateFormula 0 n) (fs : Fin n → Representative stage alpha) :
    formulaTest (phi.and psi) fs = meet (formulaTest phi fs) (formulaTest psi fs) := by
  apply test_ext
  intro x
  rw [mem_formulaTest, meet, stage.rankIntersection_val, ZFSet.mem_inter, mem_formulaTest, mem_formulaTest]
  exact stage.model.realize_and _ _ _

theorem holds_and_iff (D : Derivation stage alpha beta) (seed : Seed stage beta) {n : Nat}
    (phi psi : RankPredicateFormula 0 n) (fs : Fin n → Representative stage alpha) :
    D.Holds seed (phi.and psi) fs ↔ D.Holds seed phi fs ∧ D.Holds seed psi fs := by
  change D.Large seed _ ↔ _
  rw [formulaTest_and, D.large_meet_iff]
  rfl

theorem holds_imp_iff (D : Derivation stage alpha beta) (seed : Seed stage beta) {n : Nat}
    (phi psi : RankPredicateFormula 0 n) (fs : Fin n → Representative stage alpha) :
    D.Holds seed (phi.imp psi) fs ↔ (D.Holds seed phi fs → D.Holds seed psi fs) := by
  classical
  have h := D.holds_congr seed (phi.imp psi) (phi.and psi.not).not fs fs (fun x => by
    simp only [stage.model.realize_not, stage.model.realize_and, TransitiveClass.realize]; tauto)
  rw [h, D.holds_not_iff, D.holds_and_iff, D.holds_not_iff]
  tauto

end Derivation
end IBLP.Extender
