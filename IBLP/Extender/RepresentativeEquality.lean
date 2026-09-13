import IBLP.Extender.Witness

namespace IBLP.Extender
open FullMarkedBLP
universe u
namespace Derivation
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}

def RepEquivalent (D : Derivation stage alpha beta) (seed : Seed stage beta)
    (f g : Representative stage alpha) : Prop := D.Holds seed (.equal 0 1) ![f, g]

theorem mem_equalityTest (f g : Representative stage alpha) (x : Seed stage alpha) :
    x.val ∈ (formulaTest (.equal 0 1) ![f, g]).val ↔ f.value x = g.value x := by
  rw [mem_formulaTest]
  rfl

theorem repEquivalent_refl (D : Derivation stage alpha beta) (seed : Seed stage beta)
    (f : Representative stage alpha) : D.RepEquivalent seed f f := by
  have same : formulaTest (.equal 0 1) ![f, f] = top := test_ext (fun x => by
    rw [mem_equalityTest]
    exact iff_of_true rfl ((stage.mem_hierarchy alpha x.val).mpr x.property))
  change D.Large seed _
  rw [same]
  exact D.large_top seed

theorem repEquivalent_symm (D : Derivation stage alpha beta) (seed : Seed stage beta)
    {f g : Representative stage alpha} (h : D.RepEquivalent seed f g) : D.RepEquivalent seed g f :=
  (D.holds_congr seed (.equal 0 1) (.equal 0 1) ![f, g] ![g, f] (fun x => by
    change f.value x = g.value x ↔ g.value x = f.value x
    exact eq_comm)).mp h

theorem repEquivalent_trans (D : Derivation stage alpha beta) (seed : Seed stage beta)
    {f g h : Representative stage alpha} (fg : D.RepEquivalent seed f g) (gh : D.RepEquivalent seed g h) :
    D.RepEquivalent seed f h := by
  apply D.large_mono seed (x := meet (formulaTest (.equal 0 1) ![f, g]) (formulaTest (.equal 0 1) ![g, h]))
  · apply test_subset_of_pointwise
    intro x hx
    rw [meet, stage.rankIntersection_val, ZFSet.mem_inter, mem_equalityTest, mem_equalityTest] at hx
    exact (mem_equalityTest f h x).mpr (hx.1.trans hx.2)
  · exact (D.large_meet_iff seed _ _).mpr ⟨fg, gh⟩

def representativeSetoid (D : Derivation stage alpha beta) (seed : Seed stage beta) :
    Setoid (Representative stage alpha) where
  r := D.RepEquivalent seed
  iseqv := ⟨D.repEquivalent_refl seed, D.repEquivalent_symm seed, D.repEquivalent_trans seed⟩

noncomputable def agreement {n : Nat} (fs gs : Fin n → Representative stage alpha) : Test stage alpha :=
  finiteMeet (fun i => formulaTest (.equal 0 1) ![fs i, gs i])

theorem mem_agreement {n : Nat} (fs gs : Fin n → Representative stage alpha) (x : Seed stage alpha) :
    x.val ∈ (agreement fs gs).val ↔ ∀ i, (fs i).value x = (gs i).value x := by
  rw [agreement, mem_finiteMeet]
  simp only [mem_equalityTest]
  exact and_iff_right ((stage.mem_hierarchy alpha x.val).mpr x.property)

theorem large_agreement (D : Derivation stage alpha beta) (seed : Seed stage beta) {n : Nat}
    {fs gs : Fin n → Representative stage alpha} (h : ∀ i, D.RepEquivalent seed (fs i) (gs i)) :
    D.Large seed (agreement fs gs) := (D.large_finiteMeet_iff seed _).mpr h

theorem holds_transport (D : Derivation stage alpha beta) (seed : Seed stage beta) {n : Nat}
    (phi : RankPredicateFormula 0 n) {fs gs : Fin n → Representative stage alpha}
    (h : ∀ i, D.RepEquivalent seed (fs i) (gs i)) : D.Holds seed phi fs → D.Holds seed phi gs := by
  intro source
  apply D.large_mono seed (x := meet (agreement fs gs) (formulaTest phi fs))
  · apply test_subset_of_pointwise
    intro x hx
    rw [meet, stage.rankIntersection_val, ZFSet.mem_inter, mem_agreement, mem_formulaTest] at hx
    apply (mem_formulaTest phi gs x).mpr
    have same := funext hx.1
    simpa only [same] using hx.2
  · exact (D.large_meet_iff seed _ _).mpr ⟨D.large_agreement seed h, source⟩

theorem holds_respects (D : Derivation stage alpha beta) (seed : Seed stage beta) {n : Nat}
    (phi : RankPredicateFormula 0 n) {fs gs : Fin n → Representative stage alpha}
    (h : ∀ i, D.RepEquivalent seed (fs i) (gs i)) : D.Holds seed phi fs ↔ D.Holds seed phi gs :=
  ⟨D.holds_transport seed phi h, D.holds_transport seed phi (fun i => D.repEquivalent_symm seed (h i))⟩

end Derivation
end IBLP.Extender
