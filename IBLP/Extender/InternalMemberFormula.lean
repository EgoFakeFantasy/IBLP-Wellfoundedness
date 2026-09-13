import IBLP.Extender.PairedMembership

namespace IBLP.Extender
open FullMarkedBLP Derivation
universe u

/-- U, K, the two projections, and two seed/graph pairs. Only the
bounded membership test is submitted to K. -/
def memberTestSeparation : RankPredicateFormula 0 11 :=
  (separationMatrix pairedGraphMembership).relabelSets ![2, 3, 5, 7, 0, 8]

theorem memberTestSeparation_realize (stage : ModelStage.{u}) (v : Fin 11 → stage.model.Element) :
    stage.model.realize memberTestSeparation v ↔
      v 8 = stage.separation pairedGraphMembership ![v 2, v 3, v 5, v 7] (v 0) := by
  rw [memberTestSeparation, stage.model.realize_relabel]
  have args : v ∘ ![2, 3, 5, 7, 0, 8] =
      Fin.snoc (Fin.snoc ![v 2, v 3, v 5, v 7] (v 0)) (v 8) := by
    funext i; fin_cases i <;> rfl
  rw [args, stage.separationMatrix_iff]

def internalMemberFormula : RankPredicateFormula 0 8 :=
  (memberTestSeparation.and ((rankFormulaGraphApplies 1 8 9).and
    ((rankFormulaOrderedPair 10 4 6).and (.member 10 9)))).ex.ex.ex

theorem internalMemberFormula_realize (stage : ModelStage.{u})
    (U K p q a f b g : stage.model.Element) :
    stage.model.realize internalMemberFormula ![U, K, p, q, a, f, b, g] ↔
      ∃ X Y c : stage.model.Element,
        X = stage.separation pairedGraphMembership ![p, q, f, g] U ∧
        ZFSet.pair X.val Y.val ∈ K.val ∧ c.val = ZFSet.pair a.val b.val ∧ c.val ∈ Y.val := by
  simp [internalMemberFormula, stage.model.realize_ex, stage.model.realize_and,
    memberTestSeparation_realize, stage.model.setGraphAtom_realize,
    stage.model.setOrderedPairAtom_realize, TransitiveClass.realize]

theorem Derivation.internalMember_iff {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}
    (D : Derivation stage alpha beta) (ha : Order.IsSuccLimit alpha) (hb : Order.IsSuccLimit beta)
    (a b : Seed stage beta) (f g : Representative stage alpha) :
    stage.model.realize internalMemberFormula
      ![stage.hierarchy alpha, D.graph,
        stage.rankInclude _ (pairProjection ha false).graph, stage.rankInclude _ (pairProjection ha true).graph,
        stage.rankInclude beta a, f.graph, stage.rankInclude beta b, g.graph] ↔
      GlobalTruth.Member D ha hb ⟨a, f⟩ ⟨b, g⟩ := by
  rw [internalMemberFormula_realize, D.globalMember_pairedTest ha hb]
  let X := pairedMembershipTest ha f g
  have testEq : stage.rankInclude (Order.succ alpha) X = stage.separation pairedGraphMembership
      ![stage.rankInclude _ (pairProjection ha false).graph, stage.rankInclude _ (pairProjection ha true).graph,
        f.graph, g.graph] (stage.hierarchy alpha) := Subtype.ext rfl
  constructor
  · rintro ⟨test, image, c, ht, edge, hc, hm⟩
    have te : test = stage.rankInclude (Order.succ alpha) X := ht.trans testEq.symm
    rw [te] at edge
    obtain ⟨x, hx, hi⟩ := (D.represents.graph_exact _ _).mp edge
    have xe : x = X := Subtype.ext hx
    rw [xe] at hi
    change (pairSeed hb a b).val ∈ (D.map X).val
    rw [pairSeed_val, hi]
    exact hc ▸ hm
  · intro h
    refine ⟨stage.rankInclude (Order.succ alpha) X, stage.rankInclude (Order.succ beta) (D.map X),
      stage.orderedPair (stage.rankInclude beta a) (stage.rankInclude beta b), testEq, D.represents.2 X,
      stage.orderedPair_val _ _, ?_⟩
    change (stage.orderedPair _ _).val ∈ (D.map X).val
    rw [stage.orderedPair_val]
    simpa only [Large, pairSeed_val] using h

end IBLP.Extender
