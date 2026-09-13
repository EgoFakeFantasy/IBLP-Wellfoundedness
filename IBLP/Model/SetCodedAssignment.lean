import IBLP.Model.SetSatisfactionFormula
import IBLP.Model.SetSyntaxBooks
import IBLP.Model.SetTupleDecoding
import IBLP.Model.SetAssignmentDecoding
import IBLP.Model.SetSatisfactionInternal

namespace IBLP
open FullMarkedBLP
universe u

theorem ModelStage.setAssignmentAtCode_iff (stage : ModelStage.{u})
    (D code assignment : stage.model.Element) :
    SetAssignmentAtCode stage.model (stage.syntaxBooks 0) D code assignment ↔
      ∃ (n : Nat) (phi : RankPredicateFormula 0 n) (values : Fin n → SetDomain D.val),
        code.val = (rankSyntaxCode ⟨n, phi⟩ : Ordinal).toZFSet ∧
          assignment.val = setAssignment values := by
  have table (arity : stage.model.Element) : SetTableHolds (stage.syntaxBooks 0) ![code, arity] ↔
      ∃ (n : Nat) (phi : RankPredicateFormula 0 n),
        code.val = (rankSyntaxCode ⟨n, phi⟩ : Ordinal).toZFSet ∧ arity.val = (n : Ordinal).toZFSet := by
    have tuple : (fun i => (![code, arity] i).val) = ![code.val, arity.val] := by
      funext i
      fin_cases i <;> rfl
    change IBLP.setTuple _ ∈ zfNatRelation rankSyntaxArity ↔ _
    rw [tuple]
    exact setArityTable_iff _ _
  constructor
  · rintro ⟨arity, ht, hf⟩
    obtain ⟨n, phi, hc, ha⟩ := (table arity).mp ht
    rw [ha] at hf
    obtain ⟨values, hv⟩ := setAssignment_decode hf
    exact ⟨n, phi, values, hc, hv.symm⟩
  · rintro ⟨n, phi, values, hc, ha⟩
    refine ⟨stage.ordinal (n : Ordinal), (table _).mpr ⟨n, phi, hc, rfl⟩, ?_⟩
    rw [ha]
    exact setAssignment_function values

theorem ModelStage.setAssignmentAtCode_formula_iff (stage : ModelStage.{u})
    (D code assignment : stage.model.Element) {n : Nat} (phi : RankPredicateFormula 0 n)
    (hc : code.val = (rankSyntaxCode ⟨n, phi⟩ : Ordinal).toZFSet) :
    SetAssignmentAtCode stage.model (stage.syntaxBooks 0) D code assignment ↔
      ∃ values : Fin n → SetDomain D.val, assignment.val = setAssignment values := by
  rw [stage.setAssignmentAtCode_iff]
  constructor
  · rintro ⟨m, psi, values, hcode, ha⟩
    have hs := rankSyntaxCode_injective (Nat.cast_injective
      (Ordinal.toZFSet_injective (hc.symm.trans hcode)))
    have hn : n = m := (Sigma.mk.inj hs).1
    subst m
    exact ⟨values, ha⟩
  · rintro ⟨values, ha⟩
    exact ⟨n, phi, values, hc, ha⟩

theorem ModelStage.setAssignmentAtCode_formula (stage : ModelStage.{u})
    (D : stage.model.Element) {n : Nat} (phi : RankPredicateFormula 0 n)
    (values : Fin n → SetDomain D.val) :
    SetAssignmentAtCode stage.model (stage.syntaxBooks 0) D
      (stage.ordinal (rankSyntaxCode ⟨n, phi⟩ : Ordinal))
      ⟨setAssignment values, stage.setAssignment_mem D values⟩ :=
  (stage.setAssignmentAtCode_iff _ _ _).mpr ⟨n, phi, values, rfl, rfl⟩

end IBLP

