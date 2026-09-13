import IBLP.Model.SetSatisfactionFormula
import IBLP.Model.SetSatisfactionInternal
import IBLP.Model.SetAssignmentDecoding
import IBLP.Model.SetTupleDecoding
import IBLP.Model.SetSyntaxBooks

namespace IBLP
open FullMarkedBLP
universe u

namespace SetCodedTruthConditions
variable {stage : ModelStage.{u}} {D truth : stage.model.Element}
  (h : SetCodedTruthConditions stage.model stage.syntaxBooks D truth)

include h

/-- The single coded recursion implies all actual formula recursions.
The implication is proved by decoding the fixed constructor tables. -/
theorem toSetTruthConditions : SetTruthConditions D.val truth.val := by
  let code {n : Nat} (phi : RankPredicateFormula 0 n) :=
    stage.ordinal (rankSyntaxCode ⟨n, phi⟩ : Ordinal.{u})
  let ass {n : Nat} (v : Fin n → SetDomain D.val) : stage.model.Element :=
    ⟨setAssignment v, stage.setAssignment_mem D v⟩
  have arityTable {n : Nat} (phi : RankPredicateFormula 0 n) :
      SetTableHolds (stage.syntaxBooks 0) ![code phi, stage.ordinal (n : Ordinal.{u})] :=
    (setArityTable_iff _ _).mpr ⟨n, phi, rfl, rfl⟩
  have valid {n : Nat} (phi : RankPredicateFormula 0 n) (v : Fin n → SetDomain D.val) :
      SetAssignmentAtCode stage.model (stage.syntaxBooks 0) D (code phi) (ass v) :=
    ⟨stage.ordinal (n : Ordinal.{u}), arityTable phi, setAssignment_function v⟩
  constructor
  · intro n v
    exact h.falsum (code (.falsum : RankPredicateFormula 0 n)) (ass v) (valid _ v)
      ((setFalseTable_iff _).mpr ⟨n, rfl⟩)
  · intro n x y v
    have table : SetTableHolds (stage.syntaxBooks 2)
        ![code (.equal x y), stage.ordinal (x.val : Ordinal.{u}), stage.ordinal (y.val : Ordinal.{u})] :=
      (setEqualTable_iff _ _ _).mpr ⟨n, x, y, rfl, rfl, rfl⟩
    have eq := h.equal (code (.equal x y)) (ass v)
      (stage.ordinal (x.val : Ordinal.{u})) (stage.ordinal (y.val : Ordinal.{u}))
      (stage.model.setInclude D (v x)) (stage.model.setInclude D (v y)) (valid _ v) table
      ((setAssignment_applies_nat_iff _ _ _).mpr rfl) ((setAssignment_applies_nat_iff _ _ _).mpr rfl)
    exact eq.trans ⟨fun same => Subtype.ext (congrArg (fun z : stage.model.Element => z.val) same),
      fun same => congrArg (stage.model.setInclude D) same⟩
  · intro n x y v
    have table : SetTableHolds (stage.syntaxBooks 3)
        ![code (.member x y), stage.ordinal (x.val : Ordinal.{u}), stage.ordinal (y.val : Ordinal.{u})] :=
      (setMemberTable_iff _ _ _).mpr ⟨n, x, y, rfl, rfl, rfl⟩
    exact h.member (code (.member x y)) (ass v)
      (stage.ordinal (x.val : Ordinal.{u})) (stage.ordinal (y.val : Ordinal.{u}))
      (stage.model.setInclude D (v x)) (stage.model.setInclude D (v y)) (valid _ v) table
      ((setAssignment_applies_nat_iff _ _ _).mpr rfl) ((setAssignment_applies_nat_iff _ _ _).mpr rfl)
  · intro n p q v
    exact h.imp (code (.imp p q)) (ass v) (code p) (code q) (valid _ v)
      ((setImpTable_iff _ _ _).mpr ⟨n, p, q, rfl, rfl, rfl⟩)
  · intro n p v
    have recursion := h.all (code (.all p)) (ass v) (code p) (stage.ordinal (n : Ordinal.{u}))
      (arityTable (.all p)) (setAssignment_function v)
      ((setAllTable_iff _ _).mpr ⟨n, p, rfl, rfl⟩)
    refine recursion.trans ?_
    constructor
    · intro all x
      exact all (stage.model.setInclude D x) (ass (Fin.snoc v x)) x.property (setAssignment_snoc v x)
    · intro all x new hx same
      let x' : SetDomain D.val := ⟨x.val, hx⟩
      have eq : new.val = setAssignment (Fin.snoc v x') := by
        rw [setAssignment_snoc]
        exact same
      rw [eq]
      exact all x'

/-- Support is essential here: the formula determines the whole set T,
including rejection of malformed codes and out-of-domain assignments. -/
theorem truth_eq : truth.val = setSatisfaction D.val := by
  apply ZFSet.ext
  intro pair
  rw [mem_setSatisfaction_iff]
  constructor
  · intro member
    obtain ⟨code, assignment, hp, arity, table, function⟩ :=
      h.support (stage.model.member truth pair member) member
    change pair = ZFSet.pair code.val assignment.val at hp
    have table' : setTuple ![code.val, arity.val] ∈ zfNatRelation rankSyntaxArity := table
    obtain ⟨n, phi, codeEq, arityEq⟩ := (setArityTable_iff _ _).mp table'
    rw [arityEq] at function
    obtain ⟨v, assignmentEq⟩ := setAssignment_decode function
    refine ⟨n, phi, v, ?_, ?_⟩
    · apply (h.toSetTruthConditions.realize phi v).mp
      rw [hp, codeEq, ← assignmentEq] at member
      exact member
    · exact hp.trans (by rw [codeEq, ← assignmentEq])
  · rintro ⟨n, phi, v, satisfied, rfl⟩
    exact (h.toSetTruthConditions.realize phi v).mpr satisfied

end SetCodedTruthConditions
end IBLP
