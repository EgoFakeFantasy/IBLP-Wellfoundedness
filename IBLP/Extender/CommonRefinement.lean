import IBLP.Extender.IndexAgreement

namespace IBLP.Extender
open FullMarkedBLP Derivation
universe u
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}

/-- A simultaneous actual source projection to every seed in a finite family. -/
structure CommonRefinement (D : Derivation stage alpha beta) {n : Nat} (seeds : Fin n → Seed stage beta) where
  seed : Seed stage beta
  maps : Fin n → IndexMap stage alpha
  projects : ∀ i, D.project (maps i) seed = seeds i

namespace CommonRefinement
variable (D : Derivation stage alpha beta) {n : Nat} {seeds : Fin n → Seed stage beta}

noncomputable def canonical (ha : Order.IsSuccLimit alpha) (hb : Order.IsSuccLimit beta)
    (seeds : Fin n → Seed stage beta) : CommonRefinement D seeds where
  seed := tupleSeed hb seeds
  maps := coordinate ha
  projects := D.project_tupleSeed ha hb seeds

def Holds (R : CommonRefinement D seeds) (phi : RankPredicateFormula 0 n)
    (fs : Fin n → Representative stage alpha) : Prop :=
  D.Holds R.seed phi (fun i => (fs i).pullback (R.maps i))

/-- Truth computed at any two common refinements agrees. The proof first
merges the two common seeds, then uses actual equalizer tests for the two
composed projections; no coherence is postulated. -/
theorem holds_independent (ha : Order.IsSuccLimit alpha) (hb : Order.IsSuccLimit beta)
    (R S : CommonRefinement D seeds) (phi : RankPredicateFormula 0 n)
    (fs : Fin n → Representative stage alpha) : R.Holds D phi fs ↔ S.Holds D phi fs := by
  let common := pairSeed hb R.seed S.seed
  let r : IndexMap stage alpha := pairProjection ha false
  let s : IndexMap stage alpha := pairProjection ha true
  have hr : D.project r common = R.seed := D.project_pairSeed ha hb false R.seed S.seed
  have hs : D.project s common = S.seed := D.project_pairSeed ha hb true R.seed S.seed
  have left := D.holds_pullback_iff common phi (fun i => (fs i).pullback (R.maps i)) r
  have right := D.holds_pullback_iff common phi (fun i => (fs i).pullback (S.maps i)) s
  rw [hr] at left
  rw [hs] at right
  apply left.symm.trans
  apply Iff.trans _ right
  apply D.holds_respects common phi
  intro i
  apply D.repEquivalent_trans common (D.pullback_comp_equivalent common ha (fs i) r (R.maps i))
  apply D.repEquivalent_trans common _
    (D.repEquivalent_symm common (D.pullback_comp_equivalent common ha (fs i) s (S.maps i)))
  apply D.pullback_equivalent_of_project_eq
  rw [D.project_comp, D.project_comp, hr, hs, R.projects, S.projects]

def reindex {m : Nat} (R : CommonRefinement D seeds) (indices : Fin m → Fin n) :
    CommonRefinement D (seeds ∘ indices) where
  seed := R.seed
  maps := R.maps ∘ indices
  projects := fun i => R.projects (indices i)

end CommonRefinement
end IBLP.Extender
