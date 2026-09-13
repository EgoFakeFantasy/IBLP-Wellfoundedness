import IBLP.Extender.GlobalRelation

namespace IBLP.Extender.GlobalTruth
open FullMarkedBLP Derivation
universe u
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}
  (D : Derivation stage alpha beta) (ha : Order.IsSuccLimit alpha) (hb : Order.IsSuccLimit beta)

noncomputable def withWitness {n : Nat} (rs : Fin n → SeededRepresentative stage alpha beta)
    (R : CommonRefinement D (fun i => (rs i).seed)) (f : Representative stage alpha) :
    CommonRefinement D (fun i =>
      (Fin.snoc (α := fun _ => SeededRepresentative stage alpha beta) rs ⟨R.seed, f⟩ i).seed) where
  seed := R.seed
  maps := Fin.snoc R.maps (identityIndex ha)
  projects := by
    intro i
    cases i using Fin.lastCases with
    | last => simpa using D.project_identity ha R.seed
    | cast i => simpa using R.projects i

theorem snoc_at {n : Nat} (phi : RankPredicateFormula 0 (n + 1))
    (rs : Fin n → SeededRepresentative stage alpha beta)
    (R : CommonRefinement D (fun i => (rs i).seed)) (f : Representative stage alpha) :
    Holds D ha hb phi (Fin.snoc rs ⟨R.seed, f⟩) ↔
      D.Holds R.seed phi (Fin.snoc (fun i => (rs i).representative.pullback (R.maps i)) f) := by
  rw [at_refinement D ha hb phi _ (withWitness D ha rs R f)]
  apply D.holds_congr
  intro x
  have args : (fun i : Fin (n + 1) =>
      ((Fin.snoc (α := fun _ => SeededRepresentative stage alpha beta) rs ⟨R.seed, f⟩ i).representative.pullback
        ((withWitness D ha rs R f).maps i)).value x) =
      (fun i => Representative.value
        (Fin.snoc (α := fun _ => Representative stage alpha) (fun j => (rs j).representative.pullback (R.maps j)) f i) x) := by
    funext i
    cases i using Fin.lastCases with
    | last => simp [withWitness, Representative.pullback_value, indexValue_identity]
    | cast i => simp [withWitness]
  rw [args]

theorem exists_intro {n : Nat} (phi : RankPredicateFormula 0 (n + 1))
    (rs : Fin n → SeededRepresentative stage alpha beta) (r : SeededRepresentative stage alpha beta)
    (h : Holds D ha hb phi (Fin.snoc rs r)) : Holds D ha hb phi.ex rs := by
  let ss : Fin (n + 1) → SeededRepresentative stage alpha beta := Fin.snoc rs r
  let R := CommonRefinement.canonical D ha hb (fun i => (ss i).seed)
  have hp := (at_refinement D ha hb phi ss R).mp h
  have hlocal : D.Holds R.seed phi.ex
      (fun i : Fin n => (ss i.castSucc).representative.pullback (R.maps i.castSucc)) := by
    apply D.holds_mono R.seed phi phi.ex _ _ (fun x hx => ?_) hp
    apply (stage.model.realize_ex _ _).mpr
    refine ⟨((ss (Fin.last n)).representative.pullback (R.maps (Fin.last n))).value x, ?_⟩
    have args : (fun i => ((ss i).representative.pullback (R.maps i)).value x) =
        Fin.snoc (fun i : Fin n => ((ss i.castSucc).representative.pullback (R.maps i.castSucc)).value x)
          (((ss (Fin.last n)).representative.pullback (R.maps (Fin.last n))).value x) := by
      funext i
      cases i using Fin.lastCases with
      | last => simp
      | cast i => simp
    rwa [← args]
  have hresult := (at_indices D ha hb phi.ex ss R Fin.castSucc).mpr hlocal
  simpa [ss, Function.comp_def] using hresult

/-- Existential witnesses are constructed in one actual component, then
inserted as representatives at that component's seed. -/
theorem ex_iff {n : Nat} (phi : RankPredicateFormula 0 (n + 1))
    (rs : Fin n → SeededRepresentative stage alpha beta) :
    Holds D ha hb phi.ex rs ↔ ∃ r, Holds D ha hb phi (Fin.snoc rs r) := by
  constructor
  · intro h
    let R := CommonRefinement.canonical D ha hb (fun i => (rs i).seed)
    have hlocal := (at_refinement D ha hb phi.ex rs R).mp h
    obtain ⟨f, hf⟩ := (D.holds_ex_iff R.seed phi _).mp hlocal
    exact ⟨⟨R.seed, f⟩, (snoc_at D ha hb phi rs R f).mpr hf⟩
  · rintro ⟨r, hr⟩
    exact exists_intro D ha hb phi rs r hr

theorem all_iff {n : Nat} (phi : RankPredicateFormula 0 (n + 1))
    (rs : Fin n → SeededRepresentative stage alpha beta) :
    Holds D ha hb (.all phi) rs ↔ ∀ r, Holds D ha hb phi (Fin.snoc rs r) := by
  classical
  have equivalent := congr_formula D ha hb (.all phi) phi.not.ex.not rs (fun values => by
    simp only [stage.model.realize_not, stage.model.realize_ex, TransitiveClass.realize, not_exists, not_not])
  rw [equivalent, not_iff, ex_iff]
  simp only [not_iff, not_exists, not_not]

end IBLP.Extender.GlobalTruth
