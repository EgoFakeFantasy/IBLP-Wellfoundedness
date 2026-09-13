import IBLP.Extender.IdentityIndex

namespace IBLP.Extender
open FullMarkedBLP Derivation
universe u

/-- A representative together with the actual rank seed at which it is evaluated. -/
structure SeededRepresentative (stage : ModelStage.{u}) (alpha beta : Ordinal.{u}) where
  seed : Seed stage beta
  representative : Representative stage alpha

namespace GlobalTruth
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}
  (D : Derivation stage alpha beta) (ha : Order.IsSuccLimit alpha) (hb : Order.IsSuccLimit beta)

def Holds {n : Nat} (phi : RankPredicateFormula 0 n) (rs : Fin n → SeededRepresentative stage alpha beta) : Prop :=
  (CommonRefinement.canonical D ha hb (fun i => (rs i).seed)).Holds D phi (fun i => (rs i).representative)

theorem at_refinement {n : Nat} (phi : RankPredicateFormula 0 n)
    (rs : Fin n → SeededRepresentative stage alpha beta)
    (R : CommonRefinement D (fun i => (rs i).seed)) :
    Holds D ha hb phi rs ↔ D.Holds R.seed phi (fun i => (rs i).representative.pullback (R.maps i)) :=
  CommonRefinement.holds_independent D ha hb _ R phi _

theorem not_falsum {n : Nat} (rs : Fin n → SeededRepresentative stage alpha beta) :
    ¬Holds D ha hb .falsum rs := D.not_holds_falsum _ _

theorem not_iff {n : Nat} (phi : RankPredicateFormula 0 n)
    (rs : Fin n → SeededRepresentative stage alpha beta) :
    Holds D ha hb phi.not rs ↔ ¬Holds D ha hb phi rs := D.holds_not_iff _ _ _

theorem and_iff {n : Nat} (phi psi : RankPredicateFormula 0 n)
    (rs : Fin n → SeededRepresentative stage alpha beta) :
    Holds D ha hb (phi.and psi) rs ↔ Holds D ha hb phi rs ∧ Holds D ha hb psi rs := D.holds_and_iff _ _ _ _

theorem imp_iff {n : Nat} (phi psi : RankPredicateFormula 0 n)
    (rs : Fin n → SeededRepresentative stage alpha beta) :
    Holds D ha hb (phi.imp psi) rs ↔ (Holds D ha hb phi rs → Holds D ha hb psi rs) := D.holds_imp_iff _ _ _ _

theorem of_valid {n : Nat} (phi : RankPredicateFormula 0 n)
    (rs : Fin n → SeededRepresentative stage alpha beta)
    (h : ∀ values : Fin n → stage.model.Element, stage.model.realize phi values) : Holds D ha hb phi rs :=
  D.holds_of_pointwise _ _ _ (fun _ => h _)

theorem congr_formula {n : Nat} (phi psi : RankPredicateFormula 0 n)
    (rs : Fin n → SeededRepresentative stage alpha beta)
    (h : ∀ values : Fin n → stage.model.Element, stage.model.realize phi values ↔ stage.model.realize psi values) :
    Holds D ha hb phi rs ↔ Holds D ha hb psi rs := D.holds_congr _ _ _ _ _ (fun _ => h _)

theorem reindex_iff {n m : Nat} (phi : RankPredicateFormula 0 m)
    (rs : Fin n → SeededRepresentative stage alpha beta) (indices : Fin m → Fin n) :
    Holds D ha hb phi (rs ∘ indices) ↔ Holds D ha hb (phi.relabelSets indices) rs := by
  let R := CommonRefinement.canonical D ha hb (fun i => (rs i).seed)
  rw [at_refinement D ha hb phi (rs ∘ indices) (R.reindex D indices),
    at_refinement D ha hb (phi.relabelSets indices) rs R]
  apply D.holds_congr
  intro x
  exact (stage.model.realize_relabel phi indices
    (fun i => ((rs i).representative.pullback (R.maps i)).value x)).symm

theorem at_indices {n m : Nat} (phi : RankPredicateFormula 0 m)
    (rs : Fin n → SeededRepresentative stage alpha beta)
    (R : CommonRefinement D (fun i => (rs i).seed)) (indices : Fin m → Fin n) :
    Holds D ha hb phi (rs ∘ indices) ↔
      D.Holds R.seed phi (fun i => (rs (indices i)).representative.pullback (R.maps (indices i))) :=
  at_refinement D ha hb phi (rs ∘ indices) (R.reindex D indices)

end GlobalTruth
end IBLP.Extender
