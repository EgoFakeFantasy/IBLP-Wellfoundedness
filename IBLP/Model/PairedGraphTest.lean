import IBLP.Model.GraphMembership
import IBLP.Model.SeparationExact

namespace IBLP
open FullMarkedBLP
universe u

/-- Fixed projections, two arbitrary internal graphs, and their common
input. All four intermediate graph values are explicitly quantified. -/
def pairedGraphMembership : RankPredicateFormula 0 5 :=
  ((rankFormulaGraphApplies 0 4 5).and
    ((rankFormulaGraphApplies 1 4 6).and
      ((rankFormulaGraphApplies 2 5 7).and
        ((rankFormulaGraphApplies 3 6 8).and (.member 7 8))))).ex.ex.ex.ex

theorem pairedGraphMembership_realize (M : TransitiveClass.{u}) (p q f g x : M.Element) :
    M.realize pairedGraphMembership (Fin.snoc ![p, q, f, g] x) ↔
      ∃ a b y z : M.Element, ZFSet.pair x.val a.val ∈ p.val ∧ ZFSet.pair x.val b.val ∈ q.val ∧
        ZFSet.pair a.val y.val ∈ f.val ∧ ZFSet.pair b.val z.val ∈ g.val ∧ y.val ∈ z.val := by
  simp [pairedGraphMembership, M.realize_ex, M.realize_and, M.setGraphAtom_realize, TransitiveClass.realize]

end IBLP
