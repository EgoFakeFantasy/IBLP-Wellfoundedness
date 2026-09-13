import IBLP.Extender.ProjectionComposition

namespace IBLP.Extender
open FullMarkedBLP
universe u

namespace Derivation
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}

/-- Every finite tuple of rank seeds has a single nested-pair seed. -/
noncomputable def tupleSeed (limit : Order.IsSuccLimit beta) :
    {n : Nat} → (Fin n → Seed stage beta) → Seed stage beta
  | 0, _ => ⟨(stage.ordinal 0).val, (stage.ordinal 0).property, by
      simpa [ModelStage.ordinal] using limit.pos⟩
  | n + 1, seeds => pairSeed limit (seeds 0) (tupleSeed limit (fun i : Fin n => seeds i.succ))

theorem tupleSeed_val (limit : Order.IsSuccLimit beta) {n : Nat} (seeds : Fin n → Seed stage beta) :
    (tupleSeed limit seeds).val = setTuple (fun i => (seeds i).val) := by
  induction n with
  | zero => simp [tupleSeed, setTuple, ModelStage.ordinal]
  | succ n ih => rw [tupleSeed, pairSeed_val, ih]; rfl

theorem tupleSeed_injective (limit : Order.IsSuccLimit beta) {n : Nat} :
    Function.Injective (tupleSeed (stage := stage) limit : (Fin n → Seed stage beta) → Seed stage beta) := by
  induction n with
  | zero => intro a b _; funext i; exact Fin.elim0 i
  | succ n ih =>
    intro a b same
    have pairs := congrArg Subtype.val same
    simp only [tupleSeed, pairSeed_val, ZFSet.pair_inj] at pairs
    have tails := ih (Subtype.ext pairs.2)
    funext i
    refine Fin.cases (Subtype.ext pairs.1) (fun j => congrFun tails j) i

/-- Coordinate projections are actual total source graphs and are independent
of the particular seeds or tests. Composition first takes the tail. -/
noncomputable def coordinate (limit : Order.IsSuccLimit alpha) : {n : Nat} → Fin n → IndexMap stage alpha
  | 0, i => Fin.elim0 i
  | n + 1, i => Fin.cases (pairProjection limit false)
      (fun j : Fin n => (pairProjection limit true).comp limit (coordinate limit j)) i

theorem project_tupleSeed (D : Derivation stage alpha beta)
    (ha : Order.IsSuccLimit alpha) (hb : Order.IsSuccLimit beta)
    {n : Nat} (seeds : Fin n → Seed stage beta) (i : Fin n) :
    D.project (coordinate ha i) (tupleSeed hb seeds) = seeds i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · change D.project (pairProjection ha false) (pairSeed hb _ _) = _
      exact D.project_pairSeed ha hb false _ _
    · change D.project ((pairProjection ha true).comp ha (coordinate ha j)) (pairSeed hb _ _) = _
      rw [D.project_comp, D.project_pairSeed]
      exact ih (fun k : Fin n => seeds k.succ) j

theorem measure_coordinate_iff (D : Derivation stage alpha beta)
    (ha : Order.IsSuccLimit alpha) (hb : Order.IsSuccLimit beta)
    {n : Nat} (seeds : Fin n → Seed stage beta) (i : Fin n) (x : Test stage alpha) :
    (preimage (coordinate ha i) x).val ∈ (D.measure (tupleSeed hb seeds)).val ↔
      x.val ∈ (D.measure (seeds i)).val := by
  rw [D.measure_preimage_iff, D.project_tupleSeed]

theorem finite_directed (D : Derivation stage alpha beta)
    (ha : Order.IsSuccLimit alpha) (hb : Order.IsSuccLimit beta)
    {n : Nat} (seeds : Fin n → Seed stage beta) :
    ∃ common : Seed stage beta, ∃ projections : Fin n → IndexMap stage alpha,
      ∀ i, D.project (projections i) common = seeds i :=
  ⟨tupleSeed hb seeds, coordinate ha, D.project_tupleSeed ha hb seeds⟩

noncomputable def finiteMeet : {n : Nat} → (Fin n → Test stage alpha) → Test stage alpha
  | 0, _ => top
  | n + 1, tests => meet (tests 0) (finiteMeet (fun i : Fin n => tests i.succ))

theorem mem_finiteMeet {n : Nat} (tests : Fin n → Test stage alpha) (z : ZFSet.{u}) :
    z ∈ (finiteMeet tests).val ↔ z ∈ (stage.hierarchy alpha).val ∧ ∀ i, z ∈ (tests i).val := by
  induction n with
  | zero => simp [finiteMeet, top, ModelStage.rankHierarchy_val, endpoint]
  | succ n ih =>
    rw [finiteMeet, meet, stage.rankIntersection_val, ZFSet.mem_inter, ih]
    constructor
    · rintro ⟨first, inside, rest⟩
      exact ⟨inside, fun i => Fin.cases first rest i⟩
    · rintro ⟨inside, h⟩
      exact ⟨h 0, inside, fun i => h i.succ⟩

theorem large_finiteMeet_iff (D : Derivation stage alpha beta) (seed : Seed stage beta)
    {n : Nat} (tests : Fin n → Test stage alpha) :
    D.Large seed (finiteMeet tests) ↔ ∀ i, D.Large seed (tests i) := by
  induction n with
  | zero => exact iff_of_true (D.large_top seed) (fun i => Fin.elim0 i)
  | succ n ih =>
    rw [finiteMeet, D.large_meet_iff, ih]
    exact ⟨fun ⟨first, rest⟩ i => Fin.cases first rest i, fun h => ⟨h 0, fun i => h i.succ⟩⟩

/-- Finite simultaneous source witnesses, proved from the constructed
measures and projections rather than assumed as a compatibility axiom. -/
theorem finite_consistency (D : Derivation stage alpha beta)
    (ha : Order.IsSuccLimit alpha) (hb : Order.IsSuccLimit beta)
    {n : Nat} (seeds : Fin n → Seed stage beta) (tests : Fin n → Test stage alpha)
    (large : ∀ i, D.Large (seeds i) (tests i)) :
    ∃ z ∈ (stage.hierarchy alpha).val, ∀ i, ∃ y,
      ZFSet.pair z y ∈ (coordinate (stage := stage) ha i).graph.val ∧ y ∈ (tests i).val := by
  let pulled := fun i => preimage (coordinate ha i) (tests i)
  have hlarge : D.Large (tupleSeed hb seeds) (finiteMeet pulled) := by
    apply (D.large_finiteMeet_iff _ _).mpr
    intro i
    apply (D.large_preimage_iff _ _ _).mpr
    rw [D.project_tupleSeed]
    exact large i
  obtain ⟨z, hz⟩ := D.large_nonempty _ hlarge
  obtain ⟨inside, members⟩ := (mem_finiteMeet pulled z).mp hz
  refine ⟨z, inside, fun i => ?_⟩
  have hi := members i
  change z ∈ (preimage (coordinate ha i) (tests i)).val at hi
  rw [preimage_val, ZFSet.mem_sep] at hi
  exact hi.2

end Derivation
end IBLP.Extender
