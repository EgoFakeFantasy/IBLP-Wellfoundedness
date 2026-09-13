import IBLP.Model.GraphOperations
import IBLP.Model.Ordinals

namespace IBLP
open FullMarkedBLP
universe u

private def modelUnionMember : RankPredicateFormula 0 3 :=
  ((RankPredicateFormula.member 3 0).and (.member 2 3)).ex

private theorem modelUnionMember_realize (M : TransitiveClass.{u}) (x result z : M.Element) :
    M.realize modelUnionMember (Fin.snoc ![x, result] z) ↔
      ∃ y : M.Element, y.val ∈ x.val ∧ z.val ∈ y.val := by
  simp [modelUnionMember, M.realize_ex, M.realize_and, TransitiveClass.realize]

/-- The ordinary union axiom, as one concrete finite membership formula. -/
def modelUnionMatrix : RankPredicateFormula 0 2 :=
  .all (((RankPredicateFormula.member 2 1).imp modelUnionMember).and
    (modelUnionMember.imp (.member 2 1)))

theorem modelUnionMatrix_realize (M : TransitiveClass.{u}) (x result : M.Element) :
    M.realize modelUnionMatrix ![x, result] ↔
      ∀ z : M.Element, z.val ∈ result.val ↔ ∃ y : M.Element, y.val ∈ x.val ∧ z.val ∈ y.val := by
  change (∀ z, M.realize _ (Fin.snoc ![x, result] z)) ↔ _
  apply forall_congr'
  intro z
  rw [M.realize_and]
  change ((_ → M.realize modelUnionMember _) ∧ (M.realize modelUnionMember _ → _)) ↔ _
  rw [modelUnionMember_realize]
  exact iff_def.symm

theorem ModelStage.union_exists (stage : ModelStage.{u}) (x : stage.model.Element) :
    ∃ result : stage.model.Element, result.val = ZFSet.sUnion x.val := by
  have initial : ∀ values, ∃ result, universeClass.{u}.toTransitiveClass.realize
      modelUnionMatrix (Fin.snoc values result) := by
    intro values
    let result : universeClass.{u}.toTransitiveClass.Element := ⟨ZFSet.sUnion (values 0).val, Set.mem_univ _⟩
    refine ⟨result, ?_⟩
    have tuple : Fin.snoc values result = ![values 0, result] := by
      funext i; fin_cases i <;> rfl
    rw [tuple, modelUnionMatrix_realize]
    intro z
    change z.val ∈ ZFSet.sUnion (values 0).val ↔ _
    rw [ZFSet.mem_sUnion]
    exact ⟨fun ⟨y, hy, hz⟩ => ⟨⟨y, Set.mem_univ _⟩, hy, hz⟩,
      fun ⟨y, hy, hz⟩ => ⟨y.val, hy, hz⟩⟩
  obtain ⟨result, spec⟩ := stage.transfer_exists modelUnionMatrix initial ![x]
  have tuple : Fin.snoc ![x] result = ![x, result] := by funext i; fin_cases i <;> rfl
  rw [tuple, modelUnionMatrix_realize] at spec
  refine ⟨result, ZFSet.ext fun z => ?_⟩
  rw [ZFSet.mem_sUnion]
  constructor
  · intro hz
    obtain ⟨y, hy, inside⟩ := (spec (stage.model.member result z hz)).mp hz
    exact ⟨y.val, hy, inside⟩
  · rintro ⟨y, hy, hz⟩
    let ym := stage.model.member x y hy
    exact (spec (stage.model.member ym z hz)).mpr ⟨ym, hy, hz⟩

noncomputable def ModelStage.union (stage : ModelStage.{u}) (x : stage.model.Element) :
    stage.model.Element := (stage.union_exists x).choose

theorem ModelStage.union_val (stage : ModelStage.{u}) (x : stage.model.Element) :
    (stage.union x).val = ZFSet.sUnion x.val := (stage.union_exists x).choose_spec

private def modelRangeMember : RankPredicateFormula 0 3 :=
  (rankPredicateAtom rankGraphAppliesFormula ![0, 3, 2]).ex

private theorem modelRangeMember_realize (M : TransitiveClass.{u}) (graph result y : M.Element) :
    M.realize modelRangeMember (Fin.snoc ![graph, result] y) ↔
      ∃ x : M.Element, ZFSet.pair x.val y.val ∈ graph.val := by
  simp [modelRangeMember, M.realize_ex, M.graphFormulaAtom_realize]

/-- The range of an arbitrary actual relation graph, as a finite formula. -/
def modelRangeMatrix : RankPredicateFormula 0 2 :=
  .all (((RankPredicateFormula.member 2 1).imp modelRangeMember).and
    (modelRangeMember.imp (.member 2 1)))

theorem modelRangeMatrix_realize (M : TransitiveClass.{u}) (graph result : M.Element) :
    M.realize modelRangeMatrix ![graph, result] ↔
      ∀ y : M.Element, y.val ∈ result.val ↔ ∃ x : M.Element, ZFSet.pair x.val y.val ∈ graph.val := by
  change (∀ y, M.realize _ (Fin.snoc ![graph, result] y)) ↔ _
  apply forall_congr'
  intro y
  rw [M.realize_and]
  change ((_ → M.realize modelRangeMember _) ∧ (M.realize modelRangeMember _ → _)) ↔ _
  rw [modelRangeMember_realize]
  exact iff_def.symm

private theorem pair_right_mem_doubleUnion {graph x y : ZFSet.{u}}
    (edge : ZFSet.pair x y ∈ graph) : y ∈ ZFSet.sUnion (ZFSet.sUnion graph) := by
  apply ZFSet.mem_sUnion.mpr
  refine ⟨{x, y}, ?_, by simp⟩
  apply ZFSet.mem_sUnion.mpr
  exact ⟨ZFSet.pair x y, edge, by simp [ZFSet.pair]⟩

theorem ModelStage.graphRange_exists (stage : ModelStage.{u}) (graph : stage.model.Element) :
    ∃ result : stage.model.Element, ∀ y : stage.model.Element,
      y.val ∈ result.val ↔ ∃ x : stage.model.Element, ZFSet.pair x.val y.val ∈ graph.val := by
  have initial : ∀ values, ∃ result, universeClass.{u}.toTransitiveClass.realize
      modelRangeMatrix (Fin.snoc values result) := by
    intro values
    let result : universeClass.{u}.toTransitiveClass.Element :=
      ⟨ZFSet.sep (fun y => ∃ x, ZFSet.pair x y ∈ (values 0).val)
        (ZFSet.sUnion (ZFSet.sUnion (values 0).val)),
        Set.mem_univ _⟩
    refine ⟨result, ?_⟩
    have tuple : Fin.snoc values result = ![values 0, result] := by funext i; fin_cases i <;> rfl
    rw [tuple, modelRangeMatrix_realize]
    intro y
    dsimp only [result]
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨_, x, edge⟩
      exact ⟨⟨x, Set.mem_univ _⟩, edge⟩
    · rintro ⟨x, edge⟩
      exact ⟨pair_right_mem_doubleUnion edge, x.val, edge⟩
  obtain ⟨result, spec⟩ := stage.transfer_exists modelRangeMatrix initial ![graph]
  have tuple : Fin.snoc ![graph] result = ![graph, result] := by funext i; fin_cases i <;> rfl
  rw [tuple, modelRangeMatrix_realize] at spec
  exact ⟨result, spec⟩

/-- Countable closure first supplies the actual complete sequence graph;
the finite range formula then produces exactly its set of values in M. -/
theorem ModelStage.countableRange_exists (stage : ModelStage.{u}) (f : Nat → stage.model.Element) :
    ∃ result : stage.model.Element, ∀ y : ZFSet.{u}, y ∈ result.val ↔ ∃ n, (f n).val = y := by
  let graph : stage.model.Element := ⟨stage.model.sequenceGraph f, stage.countablyClosed f⟩
  obtain ⟨result, spec⟩ := stage.graphRange_exists graph
  refine ⟨result, fun y => ?_⟩
  constructor
  · intro hy
    obtain ⟨x, edge⟩ := (spec (stage.model.member result y hy)).mp hy
    obtain ⟨n, same⟩ := ZFSet.mem_range.mp edge
    exact ⟨n, (ZFSet.pair_inj.mp same).2⟩
  · rintro ⟨n, rfl⟩
    apply (spec (f n)).mpr
    refine ⟨stage.ordinal (n : Ordinal.{u}), ?_⟩
    change ZFSet.pair (n : Ordinal.{u}).toZFSet (f n).val ∈ stage.model.sequenceGraph f
    exact ZFSet.mem_range.mpr ⟨n, rfl⟩

theorem ModelStage.countableRange_mem (stage : ModelStage.{u}) (f : Nat → stage.model.Element) :
    ZFSet.range (fun n => (f n).val) ∈ stage.model.carrier := by
  obtain ⟨result, spec⟩ := stage.countableRange_exists f
  have same : result.val = ZFSet.range (fun n => (f n).val) := by
    apply ZFSet.ext
    intro y
    rw [spec, ZFSet.mem_range]
  exact same ▸ result.property

/-- The union of any external countable family of model sets is itself in
the model. This uses the maintained countable-closure proof and actual finite
range/union schemas, with no new model hypothesis. -/
theorem ModelStage.countableUnion_exists (stage : ModelStage.{u}) (f : Nat → stage.model.Element) :
    ∃ result : stage.model.Element, ∀ z : ZFSet.{u}, z ∈ result.val ↔ ∃ n, z ∈ (f n).val := by
  obtain ⟨range, rangeSpec⟩ := stage.countableRange_exists f
  refine ⟨stage.union range, fun z => ?_⟩
  rw [stage.union_val, ZFSet.mem_sUnion]
  constructor
  · rintro ⟨y, hy, hz⟩
    obtain ⟨n, rfl⟩ := (rangeSpec y).mp hy
    exact ⟨n, hz⟩
  · rintro ⟨n, hz⟩
    exact ⟨(f n).val, (rangeSpec _).mpr ⟨n, rfl⟩, hz⟩

end IBLP
