import IBLP.Model.Stage
import FullMarkedBLP.RankFormulaRelabel

namespace IBLP
open FullMarkedBLP
universe u

namespace TransitiveClass

theorem realize_relabel (M : TransitiveClass.{u}) {n t : Nat}
    (p : RankPredicateFormula 0 n) (indices : Fin n → Fin t) (values : Fin t → M.Element) :
    M.realize (p.relabelSets indices) values ↔ M.realize p (values ∘ indices) := by
  induction p generalizing t with
  | falsum => rfl
  | equal => rfl
  | member => rfl
  | predicate a _ => exact Fin.elim0 a
  | imp p q ihp ihq => exact imp_congr (ihp indices values) (ihq indices values)
  | all p ih =>
    apply forall_congr'
    intro x
    rw [ih]
    have compatible : Fin.snoc values x ∘ RankPredicateFormula.liftSetIndices indices =
        Fin.snoc (values ∘ indices) x := by
      funext i
      cases i using Fin.lastCases with
      | last => simp [RankPredicateFormula.liftSetIndices]
      | cast i => simp [RankPredicateFormula.liftSetIndices]
    rw [compatible]

def closeFormula : {n : Nat} → RankPredicateFormula 0 n → RankPredicateFormula 0 0
  | 0, p => p
  | _ + 1, p => closeFormula (.all p)

theorem realize_close (M : TransitiveClass.{u}) {n : Nat} (p : RankPredicateFormula 0 n) :
    M.realize (closeFormula p) Fin.elim0 ↔ ∀ values, M.realize p values := by
  induction n with
  | zero =>
    constructor
    · intro h values
      have eq : values = Fin.elim0 := by funext i; exact Fin.elim0 i
      simpa only [eq] using h
    · exact fun h => h Fin.elim0
  | succ n ih =>
    rw [closeFormula, ih]
    change (∀ values x, M.realize p (Fin.snoc values x)) ↔ _
    constructor
    · intro h values
      simpa only [Fin.snoc_init_self] using h (Fin.init values) (values (Fin.last n))
    · exact fun h values x => h (Fin.snoc values x)

end TransitiveClass

/-- 每次应用都是一个有限的一阶公式；不假定任意外部谓词的分离或替代。 -/
theorem ModelStage.transfer_schema (stage : ModelStage.{u}) {n : Nat}
    (p : RankPredicateFormula 0 n)
    (h : ∀ values, universeClass.{u}.toTransitiveClass.realize p values) :
    ∀ values, stage.model.realize p values := by
  exact (stage.model.realize_close p).mp
    (stage.transfer_closed _ ((universeClass.toTransitiveClass.realize_close p).mpr h))

theorem ModelStage.transfer_exists (stage : ModelStage.{u}) {n : Nat}
    (p : RankPredicateFormula 0 (n + 1))
    (h : ∀ values, ∃ x, universeClass.{u}.toTransitiveClass.realize p (Fin.snoc values x)) :
    ∀ values, ∃ x, stage.model.realize p (Fin.snoc values x) := by
  intro values
  apply (stage.model.realize_ex p values).mp
  apply stage.transfer_schema p.ex
  intro values
  exact (universeClass.toTransitiveClass.realize_ex p values).mpr (h values)

end IBLP
