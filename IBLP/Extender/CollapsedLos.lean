import IBLP.Extender.CollapsedModel

namespace IBLP.Extender.Ultrapower
open FullMarkedBLP FirstOrder Language Derivation
universe u
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}
  (D : Derivation stage alpha beta) (ha : Order.IsSuccLimit alpha) (hb : Order.IsSuccLimit beta)
  (inaccessible : stage.model.InternalInaccessible (stage.ordinal beta))

noncomputable def collapseComponent (seed : Seed stage beta) (f : Representative stage alpha) :
    (target D ha hb inaccessible).Element := collapseMap D ha hb inaccessible (mk D ha hb ⟨seed, f⟩)

theorem collapseComponent_constant (seed : Seed stage beta) (x : stage.model.Element) :
    collapseComponent D ha hb inaccessible seed (Representative.constant x) = embedding D ha hb inaccessible x := by
  apply Subtype.ext
  apply congrArg (collapsedValue D ha hb inaccessible)
  exact ofComponent_constant D ha hb seed x

theorem formula_component {n : Nat} (phi : membershipLanguage.Formula (Fin n))
    (seed : Seed stage beta) (fs : Fin n → Representative stage alpha) :
    phi.Realize (fun i => collapseComponent D ha hb inaccessible seed (fs i)) ↔
      D.Holds seed (rankPredicateAtom phi id) fs := by
  have transferred := (collapseEquiv D ha hb inaccessible).toElementaryEmbedding.map_formula phi
    (fun i => mk D ha hb ⟨seed, fs i⟩)
  apply transferred.trans
  exact (los_formula D ha hb phi (fun i => ⟨seed, fs i⟩)).trans
    (GlobalTruth.same_seed D ha hb seed (rankPredicateAtom phi id) fs)

theorem realize_component {n : Nat} (phi : RankPredicateFormula 0 n)
    (seed : Seed stage beta) (fs : Fin n → Representative stage alpha) :
    (target D ha hb inaccessible).realize phi (fun i => collapseComponent D ha hb inaccessible seed (fs i)) ↔
      D.Holds seed phi fs := by
  rw [(target D ha hb inaccessible).realize_toFormula, formula_component]
  apply D.holds_congr
  intro x
  rw [stage.model.realize_atom, Function.comp_id, ← stage.model.realize_toFormula]

end IBLP.Extender.Ultrapower
