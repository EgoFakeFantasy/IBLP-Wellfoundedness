import IBLP.Model.SetSyntaxBooksImage
import IBLP.Model.SetSatisfactionFormulaElementary

namespace IBLP
open FullMarkedBLP FirstOrder Language
universe u

abbrev StagePredicate (n : Nat) := ∀ stage : ModelStage.{u}, (Fin n → stage.model.Element) → Prop

/-- One actual finite membership formula, uniformly interpreted in every
model stage. The only fixed parameters are the six already constructed
syntax books; every elementary map is proved to preserve them. -/
def UniformDefinable {n : Nat} (P : StagePredicate.{u} n) : Prop :=
  ∃ phi : RankPredicateFormula 0 (6 + n), ∀ stage values,
    stage.model.realize phi (Fin.append stage.syntaxBooks values) ↔ P stage values

namespace UniformDefinable
variable {n m : Nat} {P Q : StagePredicate.{u} n}

theorem congr (defined : UniformDefinable P) (same : ∀ stage values, P stage values ↔ Q stage values) :
    UniformDefinable Q := by
  obtain ⟨phi, meaning⟩ := defined
  exact ⟨phi, fun stage values => (meaning stage values).trans (same stage values)⟩

theorem truth : UniformDefinable (fun (_ : ModelStage.{u}) (_ : Fin n → _) => True) :=
  ⟨RankPredicateFormula.falsum.not, fun _ _ => by simp [TransitiveClass.realize, RankPredicateFormula.not]⟩

theorem falsity : UniformDefinable (fun (_ : ModelStage.{u}) (_ : Fin n → _) => False) :=
  ⟨RankPredicateFormula.falsum, fun _ _ => Iff.rfl⟩

theorem constant (p : Prop) : UniformDefinable (fun (_ : ModelStage.{u}) (_ : Fin n → _) => p) := by
  classical
  by_cases hp : p
  · exact truth.congr (fun _ _ => by simp only [hp])
  · exact falsity.congr (fun _ _ => by simp only [hp])

theorem and (left : UniformDefinable P) (right : UniformDefinable Q) :
    UniformDefinable (fun stage values => P stage values ∧ Q stage values) := by
  obtain ⟨p, hp⟩ := left
  obtain ⟨q, hq⟩ := right
  exact ⟨p.and q, fun stage values => (stage.model.realize_and p q _).trans
    (and_congr (hp stage values) (hq stage values))⟩

theorem not (defined : UniformDefinable P) : UniformDefinable (fun stage values => ¬ P stage values) := by
  obtain ⟨phi, meaning⟩ := defined
  exact ⟨phi.not, fun stage values => (stage.model.realize_not phi _).trans (not_congr (meaning stage values))⟩

theorem imp (left : UniformDefinable P) (right : UniformDefinable Q) :
    UniformDefinable (fun stage values => P stage values → Q stage values) := by
  classical
  exact (left.and right.not).not.congr (fun _ _ => by tauto)

theorem exists_last {P : StagePredicate.{u} (n + 1)} (defined : UniformDefinable P) :
    UniformDefinable (fun stage values => ∃ x, P stage (Fin.snoc values x)) := by
  obtain ⟨phi, meaning⟩ := defined
  refine ⟨phi.ex, ?_⟩
  intro stage values
  rw [stage.model.realize_ex]
  apply exists_congr
  intro x
  rw [← Fin.append_snoc]
  exact meaning stage (Fin.snoc values x)

theorem relabel (defined : UniformDefinable P) (f : Fin n → Fin m) :
    UniformDefinable (fun stage values => P stage (values ∘ f)) := by
  obtain ⟨phi, meaning⟩ := defined
  let indices : Fin (6 + n) → Fin (6 + m) :=
    Fin.addCases (Fin.castAdd m) (fun i => Fin.natAdd 6 (f i))
  refine ⟨phi.relabelSets indices, ?_⟩
  intro stage values
  rw [stage.model.realize_relabel]
  have tuple : Fin.append stage.syntaxBooks values ∘ indices =
      Fin.append stage.syntaxBooks (values ∘ f) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [indices, Function.comp_def]
  rw [tuple]
  exact meaning stage (values ∘ f)

theorem of_matrix (phi : RankPredicateFormula 0 n) :
    UniformDefinable (fun stage values => stage.model.realize phi values) := by
  refine ⟨phi.relabelSets (Fin.natAdd 6), ?_⟩
  intro stage values
  rw [stage.model.realize_relabel]
  have tuple : Fin.append stage.syntaxBooks values ∘ Fin.natAdd 6 = values := by
    funext i
    simp
  rw [tuple]

/-- Every uniformly defined predicate is reflected in both directions,
including its existential witnesses. Syntax-book preservation is proved
internally and is not an additional caller assumption. -/
theorem reflect_iff (defined : UniformDefinable P) (source target : ModelStage.{u})
    (j : source.model.ElementaryMap target.model) (values : Fin n → source.model.Element) :
    P target (j ∘ values) ↔ P source values := by
  obtain ⟨phi, meaning⟩ := defined
  have transferred := j.realize_iff phi (Fin.append source.syntaxBooks values)
  have tuple : j ∘ Fin.append source.syntaxBooks values =
      Fin.append target.syntaxBooks (j ∘ values) := by
    funext i
    refine Fin.addCases (fun k => ?_) (fun k => ?_) i
    · simp only [Function.comp_apply, Fin.append_left]
      exact source.syntaxBooks_image target j k
    · simp
  rw [tuple, meaning target, meaning source] at transferred
  exact transferred

end UniformDefinable
end IBLP
