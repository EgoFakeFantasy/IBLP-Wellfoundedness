import IBLP.Extender.GlobalLos

namespace IBLP.Extender
open FullMarkedBLP FirstOrder Language Derivation
universe u
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}

theorem GlobalTruth.same_seed (D : Derivation stage alpha beta)
    (ha : Order.IsSuccLimit alpha) (hb : Order.IsSuccLimit beta) (seed : Seed stage beta)
    {n : Nat} (phi : RankPredicateFormula 0 n) (fs : Fin n → Representative stage alpha) :
    GlobalTruth.Holds D ha hb phi (fun i => ⟨seed, fs i⟩) ↔ D.Holds seed phi fs := by
  let R : CommonRefinement D (fun _ : Fin n => seed) :=
    ⟨seed, fun _ => identityIndex ha, fun _ => D.project_identity ha seed⟩
  rw [GlobalTruth.at_refinement D ha hb phi _ R]
  apply D.holds_congr
  intro x
  have args : (fun i => ((fs i).pullback (R.maps i)).value x) = fun i => (fs i).value x := by
    funext i
    exact (Representative.pullback_value _ _ _).trans (congrArg (fs i).value (indexValue_identity ha x))
  rw [args]

namespace Ultrapower
variable (D : Derivation stage alpha beta) (ha : Order.IsSuccLimit alpha) (hb : Order.IsSuccLimit beta)

theorem mk_same_seed_eq_iff (seed : Seed stage beta) (f g : Representative stage alpha) :
    mk D ha hb ⟨seed, f⟩ = mk D ha hb ⟨seed, g⟩ ↔ D.RepEquivalent seed f g := by
  rw [mk_eq_iff]
  have h := GlobalTruth.same_seed D ha hb seed (.equal 0 1) ![f, g]
  have args : (fun i : Fin 2 => (⟨seed, ![f, g] i⟩ : SeededRepresentative stage alpha beta)) =
      ![⟨seed, f⟩, ⟨seed, g⟩] := by funext i; fin_cases i <;> rfl
  rw [args] at h
  exact h

def ofComponent (seed : Seed stage beta) : UltrapowerAt D seed → Ultrapower D ha hb :=
  fun x => Quotient.liftOn x (fun f => mk D ha hb ⟨seed, f⟩) (by
    intro f g h
    exact (mk_same_seed_eq_iff D ha hb seed f g).mpr h)

theorem ofComponent_mk (seed : Seed stage beta) (f : Representative stage alpha) :
    ofComponent D ha hb seed (UltrapowerAt.mk D seed f) = mk D ha hb ⟨seed, f⟩ := rfl

noncomputable def componentEmbedding (seed : Seed stage beta) :
    ElementaryEmbedding membershipLanguage (UltrapowerAt D seed) (Ultrapower D ha hb) where
  toFun := ofComponent D ha hb seed
  map_formula' := by
    classical
    intro n phi values
    let fs : Fin n → Representative stage alpha :=
      fun i => Classical.choose (UltrapowerAt.mk_surjective D seed (values i))
    have same : UltrapowerAt.mk D seed ∘ fs = values :=
      funext (fun i => Classical.choose_spec (UltrapowerAt.mk_surjective D seed (values i)))
    rw [← same]
    change phi.Realize (mk D ha hb ∘ (fun i => ⟨seed, fs i⟩)) ↔ _
    rw [los_formula, GlobalTruth.same_seed, UltrapowerAt.los_formula]

theorem componentEmbedding_mk (seed : Seed stage beta) (f : Representative stage alpha) :
    componentEmbedding D ha hb seed (UltrapowerAt.mk D seed f) = mk D ha hb ⟨seed, f⟩ := rfl

theorem exists_component (x : Ultrapower D ha hb) :
    ∃ seed, ∃ y : UltrapowerAt D seed, ofComponent D ha hb seed y = x := by
  obtain ⟨r, rfl⟩ := mk_surjective D ha hb x
  exact ⟨r.seed, UltrapowerAt.mk D r.seed r.representative, rfl⟩

noncomputable def constantEmbedding :
    ElementaryEmbedding membershipLanguage stage.model.Element (Ultrapower D ha hb) :=
  (componentEmbedding D ha hb (tupleSeed hb ![])).comp (UltrapowerAt.constantEmbedding D (tupleSeed hb ![]))

theorem constantEmbedding_mk (x : stage.model.Element) :
    constantEmbedding D ha hb x = mk D ha hb ⟨tupleSeed hb ![], Representative.constant x⟩ := rfl

theorem constant_seed_independent (a b : Seed stage beta) (x : stage.model.Element) :
    mk D ha hb ⟨a, Representative.constant x⟩ = mk D ha hb ⟨b, Representative.constant x⟩ := by
  let rs : Fin 2 → SeededRepresentative stage alpha beta :=
    ![⟨a, Representative.constant x⟩, ⟨b, Representative.constant x⟩]
  let R := CommonRefinement.canonical D ha hb (fun i => (rs i).seed)
  apply (mk_eq_iff D ha hb _ _).mpr
  apply (GlobalTruth.equivalent_at D ha hb rs R 0 1).mpr
  apply D.holds_of_pointwise
  intro z
  change ((Representative.constant x).pullback (R.maps 0)).value z =
    ((Representative.constant x).pullback (R.maps 1)).value z
  simp only [Representative.pullback_value, Representative.constant_value]

theorem ofComponent_constant (seed : Seed stage beta) (x : stage.model.Element) :
    ofComponent D ha hb seed (UltrapowerAt.constantEmbedding D seed x) = constantEmbedding D ha hb x :=
  constant_seed_independent D ha hb seed (tupleSeed hb ![]) x

theorem ofComponent_transition (seed : Seed stage beta) (p : IndexMap stage alpha)
    (x : UltrapowerAt D (D.project p seed)) :
    ofComponent D ha hb seed (UltrapowerAt.transition D seed p x) =
      ofComponent D ha hb (D.project p seed) x := by
  obtain ⟨f, rfl⟩ := UltrapowerAt.mk_surjective D (D.project p seed) x
  let rs : Fin 2 → SeededRepresentative stage alpha beta :=
    ![⟨seed, f.pullback p⟩, ⟨D.project p seed, f⟩]
  let R : CommonRefinement D (fun i => (rs i).seed) :=
    ⟨seed, ![identityIndex ha, p], by
      intro i; fin_cases i
      · exact D.project_identity ha seed
      · rfl⟩
  apply (mk_eq_iff D ha hb _ _).mpr
  apply (GlobalTruth.equivalent_at D ha hb rs R 0 1).mpr
  apply D.holds_of_pointwise
  intro z
  change ((f.pullback p).pullback (identityIndex ha)).value z = (f.pullback p).value z
  rw [Representative.pullback_value, indexValue_identity]

end Ultrapower
end IBLP.Extender
