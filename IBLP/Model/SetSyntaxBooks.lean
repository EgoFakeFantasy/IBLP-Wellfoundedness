import IBLP.Model.CountableUnion
import IBLP.Model.SetSatisfactionFormulaAtoms
import FullMarkedBLP.RankSyntaxData

namespace IBLP
open FullMarkedBLP
universe u

/-- Countable closure contains every relation on finite natural tuples.
The proof constructs a countable family of singleton tuple sets, including
empty slots when the relation's countable enumeration has no entry. -/
theorem ModelStage.zfNatRelation_mem (stage : ModelStage.{u}) {n : Nat}
    (relation : (Fin n → Nat) → Prop) : zfNatRelation.{u} relation ∈ stage.model.carrier := by
  let T := {v : Fin n → Nat // relation v}
  letI : Encodable T := Encodable.ofCountable T
  let tuple (t : T) : stage.model.Element :=
    stage.setTuple (fun i => stage.ordinal (t.val i : Ordinal.{u}))
  have tuple_val (t : T) : (tuple t).val = zfNatTuple t.val := by
    rw [show tuple t = stage.setTuple _ from rfl, stage.setTuple_val]
    exact setTuple_nat t.val
  let pieces (k : Nat) : stage.model.Element :=
    match Encodable.decode (α := T) k with
    | none => stage.ordinal 0
    | some t => stage.finiteSet [tuple t]
  obtain ⟨result, spec⟩ := stage.countableUnion_exists pieces
  have same : result.val = zfNatRelation.{u} relation := by
    apply ZFSet.ext
    intro z
    rw [spec, zfNatRelation, ZFSet.mem_range]
    constructor
    · rintro ⟨k, member⟩
      cases decoded : Encodable.decode (α := T) k with
      | none =>
        simp only [pieces, decoded, ordinal, Ordinal.toZFSet_zero, ZFSet.notMem_empty] at member
      | some t =>
        have value : (tuple t).val = z := by
          simpa only [pieces, decoded, stage.mem_finiteSet, List.mem_singleton, exists_eq_left] using member
        exact ⟨t, (tuple_val t).symm.trans value⟩
    · rintro ⟨t, value⟩
      refine ⟨Encodable.encode t, ?_⟩
      simp only [pieces, Encodable.encodek, stage.mem_finiteSet, List.mem_singleton, exists_eq_left]
      exact (tuple_val t).trans value
  exact same ▸ result.property

noncomputable def ModelStage.natRelation (stage : ModelStage.{u}) {n : Nat}
    (relation : (Fin n → Nat) → Prop) : stage.model.Element :=
  ⟨zfNatRelation relation, stage.zfNatRelation_mem relation⟩

theorem ModelStage.natRelation_val (stage : ModelStage.{u}) {n : Nat}
    (relation : (Fin n → Nat) → Prop) :
    (stage.natRelation relation).val = zfNatRelation.{u} relation := rfl

/-- The six fixed pure-syntax tables, in the order used by the satisfaction
formula: arity, falsum, equality, membership, implication, universal quantifier. -/
noncomputable def zfSyntaxBooks : Fin 6 → ZFSet.{u} :=
  ![zfNatRelation rankSyntaxArity, zfNatRelation rankSyntaxFalse,
    zfNatRelation rankSyntaxEqual, zfNatRelation rankSyntaxMember,
    zfNatRelation rankSyntaxImp, zfNatRelation rankSyntaxAll]

noncomputable def ModelStage.syntaxBooks (stage : ModelStage.{u}) : Fin 6 → stage.model.Element :=
  ![stage.natRelation rankSyntaxArity, stage.natRelation rankSyntaxFalse,
    stage.natRelation rankSyntaxEqual, stage.natRelation rankSyntaxMember,
    stage.natRelation rankSyntaxImp, stage.natRelation rankSyntaxAll]

theorem ModelStage.syntaxBooks_val (stage : ModelStage.{u}) (i : Fin 6) :
    (stage.syntaxBooks i).val = zfSyntaxBooks.{u} i := by
  fin_cases i <;> rfl

theorem zfSyntaxBooks_rank_le (i : Fin 6) : (zfSyntaxBooks.{u} i).rank ≤ Ordinal.omega0 := by
  fin_cases i <;> exact zfNatRelation_rank_le _

end IBLP
