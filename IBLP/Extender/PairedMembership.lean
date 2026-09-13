import IBLP.Extender.IndexRepresentative
import IBLP.Model.PairedGraphTest

namespace IBLP.Extender.Derivation
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}

noncomputable def pairedMembershipTest (ha : Order.IsSuccLimit alpha)
    (f g : Representative stage alpha) : Test stage alpha :=
  let test := stage.separation pairedGraphMembership
    ![stage.rankInclude _ (pairProjection ha false).graph, stage.rankInclude _ (pairProjection ha true).graph,
      f.graph, g.graph] (stage.hierarchy alpha)
  subsetTest top test (by
    intro x hx
    exact ((stage.mem_separation _ _ _ (stage.model.member test x hx)).mp hx).1)

theorem pairedMembershipTest_eq (ha : Order.IsSuccLimit alpha) (f g : Representative stage alpha) :
    pairedMembershipTest ha f g = formulaTest (.member 0 1)
      ![f.pullback (pairProjection ha false), g.pullback (pairProjection ha true)] := by
  apply test_ext
  intro x
  rw [mem_formulaTest]
  change (stage.rankInclude alpha x).val ∈
    (stage.separation pairedGraphMembership
      ![stage.rankInclude _ (pairProjection ha false).graph, stage.rankInclude _ (pairProjection ha true).graph,
        f.graph, g.graph] (stage.hierarchy alpha)).val ↔
      ((f.pullback (pairProjection ha false)).value x).val ∈ ((g.pullback (pairProjection ha true)).value x).val
  rw [stage.mem_separation, pairedGraphMembership_realize, Representative.pullback_value, Representative.pullback_value]
  let p := pairProjection (stage := stage) ha false
  let q := pairProjection (stage := stage) ha true
  constructor
  · rintro ⟨_, a, b, y, z, ha', hb', hf, hg, hm⟩
    have ae : a = stage.rankInclude alpha (Representative.indexValue p x) :=
      (p.toRepresentative.value_unique x a ha').trans (p.toRepresentative_value x)
    have be : b = stage.rankInclude alpha (Representative.indexValue q x) :=
      (q.toRepresentative.value_unique x b hb').trans (q.toRepresentative_value x)
    rw [ae] at hf
    rw [be] at hg
    have ye := f.value_unique (Representative.indexValue p x) y hf
    have ze := g.value_unique (Representative.indexValue q x) z hg
    rwa [ye, ze] at hm
  · intro hm
    exact ⟨(stage.mem_hierarchy alpha x.val).mpr x.property,
      stage.rankInclude _ (Representative.indexValue p x), stage.rankInclude _ (Representative.indexValue q x),
      f.value (Representative.indexValue p x), g.value (Representative.indexValue q x),
      Representative.indexValue_edge p x, Representative.indexValue_edge q x,
      f.value_edge _, g.value_edge _, hm⟩

theorem globalMember_pairedTest (D : Derivation stage alpha beta)
    (ha : Order.IsSuccLimit alpha) (hb : Order.IsSuccLimit beta)
    (a b : Seed stage beta) (f g : Representative stage alpha) :
    GlobalTruth.Member D ha hb ⟨a, f⟩ ⟨b, g⟩ ↔ D.Large (pairSeed hb a b) (pairedMembershipTest ha f g) := by
  let family : Fin 2 → SeededRepresentative stage alpha beta := ![⟨a, f⟩, ⟨b, g⟩]
  let R : CommonRefinement D (fun i => (family i).seed) :=
    ⟨pairSeed hb a b, ![pairProjection ha false, pairProjection ha true], by
      intro i; fin_cases i
      · exact D.project_pairSeed ha hb false a b
      · exact D.project_pairSeed ha hb true a b⟩
  have h := GlobalTruth.member_at D ha hb family R 0 1
  rw [pairedMembershipTest_eq]
  exact h

end IBLP.Extender.Derivation
