import IBLP.Extender.InternalMemberFormula
import IBLP.Extender.LocalCodes

namespace IBLP.Extender
open FullMarkedBLP Derivation
universe u

def codeMemberBody : RankPredicateFormula 0 10 :=
  internalMemberFormula.relabelSets ![0, 1, 2, 3, 6, 7, 8, 9]

theorem codeMemberBody_realize (M : TransitiveClass.{u}) (v : Fin 10 → M.Element) :
    M.realize codeMemberBody v ↔ M.realize internalMemberFormula ![v 0, v 1, v 2, v 3, v 6, v 7, v 8, v 9] := by
  rw [codeMemberBody, M.realize_relabel]
  have args : v ∘ ![0, 1, 2, 3, 6, 7, 8, 9] = ![v 0, v 1, v 2, v 3, v 6, v 7, v 8, v 9] := by
    funext i; fin_cases i <;> rfl
  rw [args]

def codeMemberFormula : RankPredicateFormula 0 6 :=
  ((rankFormulaOrderedPair 4 6 7).and ((rankFormulaOrderedPair 5 8 9).and codeMemberBody)).ex.ex.ex.ex

theorem codeMemberFormula_realize (M : TransitiveClass.{u}) (U K p q c d : M.Element) :
    M.realize codeMemberFormula ![U, K, p, q, c, d] ↔
      ∃ a f b g : M.Element, c.val = ZFSet.pair a.val f.val ∧ d.val = ZFSet.pair b.val g.val ∧
        M.realize internalMemberFormula ![U, K, p, q, a, f, b, g] := by
  simp [codeMemberFormula, M.realize_ex, M.realize_and, M.setOrderedPairAtom_realize,
    codeMemberBody_realize]

namespace LocalCodes
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}
  (D : Derivation stage alpha beta) (ha : Order.IsSuccLimit alpha) (hb : Order.IsSuccLimit beta)
  (bound : stage.model.Element)

noncomputable def element (c : SetDomain (domain stage alpha beta bound).val) : stage.model.Element :=
  stage.model.member (domain stage alpha beta bound) c.val c.property

theorem codeMember_iff (c d : SetDomain (domain stage alpha beta bound).val) :
    stage.model.realize codeMemberFormula
      ![stage.hierarchy alpha, D.graph,
        stage.rankInclude _ (pairProjection ha false).graph, stage.rankInclude _ (pairProjection ha true).graph,
        element bound c, element bound d] ↔
      GlobalTruth.Member D ha hb (representative bound c) (representative bound d) := by
  rw [codeMemberFormula_realize]
  let r := representative bound c
  let s := representative bound d
  constructor
  · rintro ⟨a, f, b, g, hc, hd, h⟩
    have pc : ZFSet.pair r.seed.val r.representative.graph.val = ZFSet.pair a.val f.val :=
      (code_val bound c).symm.trans hc
    have pd : ZFSet.pair s.seed.val s.representative.graph.val = ZFSet.pair b.val g.val :=
      (code_val bound d).symm.trans hd
    have ae : a = stage.rankInclude beta r.seed := Subtype.ext (ZFSet.pair_inj.mp pc).1.symm
    have fe : f = r.representative.graph := Subtype.ext (ZFSet.pair_inj.mp pc).2.symm
    have be : b = stage.rankInclude beta s.seed := Subtype.ext (ZFSet.pair_inj.mp pd).1.symm
    have ge : g = s.representative.graph := Subtype.ext (ZFSet.pair_inj.mp pd).2.symm
    rw [ae, fe, be, ge] at h
    exact (D.internalMember_iff ha hb r.seed s.seed r.representative s.representative).mp h
  · intro h
    exact ⟨stage.rankInclude beta r.seed, r.representative.graph, stage.rankInclude beta s.seed,
      s.representative.graph, code_val bound c, code_val bound d,
      (D.internalMember_iff ha hb r.seed s.seed r.representative s.representative).mpr h⟩

end LocalCodes
end IBLP.Extender
