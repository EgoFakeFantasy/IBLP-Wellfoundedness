import IBLP.Model.UniformDefinability

namespace IBLP.UniformDefinable
universe u
variable {n : Nat}

theorem list_all {ι : Type*} (indices : List ι) (P : ι → StagePredicate.{u} n)
    (defined : ∀ i ∈ indices, UniformDefinable (P i)) :
    UniformDefinable (fun stage values => ∀ i ∈ indices, P i stage values) := by
  induction indices with
  | nil => exact truth.congr (fun _ _ => by simp)
  | cons i rest ih =>
    have head := defined i (List.mem_cons_self ..)
    have tail := ih (fun j member => defined j (List.mem_cons_of_mem _ member))
    exact (head.and tail).congr (fun _ _ => by simp)

theorem finite_all {ι : Type*} [Fintype ι] (P : ι → StagePredicate.{u} n)
    (defined : ∀ i, UniformDefinable (P i)) :
    UniformDefinable (fun stage values => ∀ i, P i stage values) := by
  classical
  exact (list_all Finset.univ.toList P (fun i _ => defined i)).congr (fun _ _ => by simp)

/-- A finite block of actual set witnesses is represented by finitely
many first-order existential quantifiers, for any metalevel block size. -/
theorem exists_fin (k : Nat) {P : StagePredicate.{u} (n + k)} (defined : UniformDefinable P) :
    UniformDefinable (fun stage values => ∃ xs : Fin k → stage.model.Element,
      P stage (Fin.append values xs)) := by
  induction k with
  | zero =>
    exact defined.congr (by
      intro stage values
      constructor
      · intro value
        exact ⟨Fin.elim0, by simpa using value⟩
      · rintro ⟨xs, value⟩
        have same : xs = Fin.elim0 := funext (fun i => Fin.elim0 i)
        subst xs
        simpa using value)
  | succ k ih =>
    have smaller := ih defined.exists_last
    exact smaller.congr (by
      intro stage values
      constructor
      · rintro ⟨xs, x, value⟩
        exact ⟨Fin.snoc xs x, by simpa only [Fin.append_snoc] using value⟩
      · rintro ⟨xs, value⟩
        refine ⟨Fin.init xs, xs (Fin.last k), ?_⟩
        rw [← Fin.append_snoc, Fin.snoc_init_self]
        exact value)

end IBLP.UniformDefinable
