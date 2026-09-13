import IBLP.Model.CountableUnion
import IBLP.Encoding.FiniteImage
import IBLP.Model.Inaccessible
import FullMarkedBLP.RankSequenceGraph

namespace IBLP
open FullMarkedBLP
universe u

namespace ModelStage

noncomputable def countableRange (stage : ModelStage.{u}) (f : Nat → stage.model.Element) :
    stage.model.Element := ⟨ZFSet.range (fun n => (f n).val), stage.countableRange_mem f⟩

theorem countableRange_val (stage : ModelStage.{u}) (f : Nat → stage.model.Element) :
    (stage.countableRange f).val = ZFSet.range (fun n => (f n).val) := rfl

noncomputable def countableGraph (stage : ModelStage.{u}) (f : Nat → stage.model.Element) :
    stage.model.Element := ⟨stage.model.sequenceGraph f, stage.countablyClosed f⟩

theorem countableGraph_function (stage : ModelStage.{u}) (f : Nat → stage.model.Element) :
    ZFSet.IsFunc (stage.ordinal Ordinal.omega0).val (stage.countableRange f).val
      (stage.countableGraph f).val := by
  constructor
  · intro p hp
    obtain ⟨n, rfl⟩ := ZFSet.mem_range.mp hp
    exact ZFSet.pair_mem_prod.mpr ⟨(natZFSetOmegaEquiv n).property, ZFSet.mem_range.mpr ⟨n, rfl⟩⟩
  · intro a ha
    let n := natZFSetOmegaEquiv.symm ⟨a, ha⟩
    have hn : (n : Ordinal.{u}).toZFSet = a :=
      congrArg Subtype.val (natZFSetOmegaEquiv.apply_symm_apply ⟨a, ha⟩)
    refine ⟨(f n).val, ?_, ?_⟩
    · exact ZFSet.mem_range.mpr ⟨n, by rw [hn]⟩
    · intro b hb
      obtain ⟨m, hm⟩ := ZFSet.mem_range.mp hb
      obtain ⟨hm, value⟩ := ZFSet.pair_inj.mp hm
      have same : m = n := Nat.cast_injective (Ordinal.toZFSet_injective (hm.trans hn.symm))
      simpa only [same] using value.symm

theorem countableGraph_range (stage : ModelStage.{u}) (f : Nat → stage.model.Element) :
    stage.model.realize modelRangeMatrix ![stage.countableGraph f, stage.countableRange f] := by
  rw [modelRangeMatrix_realize]
  intro y
  constructor
  · intro hy
    obtain ⟨n, hn⟩ := ZFSet.mem_range.mp hy
    refine ⟨stage.ordinal (n : Ordinal.{u}), ZFSet.mem_range.mpr ⟨n, ?_⟩⟩
    change ZFSet.pair _ (f n).val = ZFSet.pair _ y.val
    rw [hn]
    rfl
  · rintro ⟨x, edge⟩
    obtain ⟨n, hn⟩ := ZFSet.mem_range.mp edge
    exact ZFSet.mem_range.mpr ⟨n, (ZFSet.pair_inj.mp hn).2⟩

variable (source target : ModelStage.{u}) (j : source.model.ElementaryMap target.model)

/-- The least nonzero limit ordinal is definable by one finite formula. -/
theorem ordinal_omega_image : j (source.ordinal Ordinal.omega0) = target.ordinal Ordinal.omega0 := by
  have h := j.map_formula rankFirstLimitFormula ![source.ordinal Ordinal.omega0]
  have tuple : j ∘ ![source.ordinal Ordinal.omega0] = ![j (source.ordinal Ordinal.omega0)] := by
    funext i; fin_cases i; rfl
  rw [tuple, target.model.firstLimitFormula_absolute, source.model.firstLimitFormula_absolute] at h
  apply Subtype.ext
  apply (setFirstLimit_ordinal_iff ((j.isOrdinal_iff _).mpr (ZFSet.isOrdinal_toZFSet _))).mp
  exact h.mpr setFirstLimit_omega

/-- A complete omega-domain graph has no new coordinates under an elementary
map: every coordinate is a standard natural, already proved fixed. -/
theorem countableGraph_image (f : Nat → source.model.Element) :
    j (source.countableGraph f) = target.countableGraph (j ∘ f) := by
  have function := (j.function_iff (source.countableGraph f)
    (source.ordinal Ordinal.omega0) (source.countableRange f)).mpr (source.countableGraph_function f)
  rw [source.ordinal_omega_image target j] at function
  have edge (n : Nat) : ZFSet.pair (n : Ordinal.{u}).toZFSet (j (f n)).val ∈
      (j (source.countableGraph f)).val := by
    have h := (j.graphApplies_iff (source.countableGraph f) (source.ordinal (n : Ordinal.{u})) (f n)).mpr
      ((source.model.graphApplies_absolute _ _ _).mpr (ZFSet.mem_range.mpr ⟨n, rfl⟩))
    rw [source.ordinal_nat_image target j] at h
    exact (target.model.graphApplies_absolute _ _ _).mp h
  apply Subtype.ext
  apply ZFSet.ext
  intro p
  constructor
  · intro hp
    obtain ⟨a, ha, b, _, rfl⟩ := ZFSet.mem_prod.mp (function.1 hp)
    let n := natZFSetOmegaEquiv.symm ⟨a, ha⟩
    have hn : (n : Ordinal.{u}).toZFSet = a :=
      congrArg Subtype.val (natZFSetOmegaEquiv.apply_symm_apply ⟨a, ha⟩)
    have actual := edge n
    rw [hn] at actual
    have value := (function.2 a ha).unique actual hp
    exact ZFSet.mem_range.mpr ⟨n, by simp only [Function.comp_apply, hn, value]⟩
  · intro hp
    obtain ⟨n, rfl⟩ := ZFSet.mem_range.mp hp
    exact edge n

/-- The finite range formula, together with the complete image sequence
graph, excludes extra elements in the image of an arbitrary countable set. -/
theorem countableRange_image (f : Nat → source.model.Element) :
    j (source.countableRange f) = target.countableRange (j ∘ f) := by
  have h := j.realize_iff modelRangeMatrix ![source.countableGraph f, source.countableRange f]
  have tuple : j ∘ ![source.countableGraph f, source.countableRange f] =
      ![j (source.countableGraph f), j (source.countableRange f)] := by
    funext i; fin_cases i <;> rfl
  rw [tuple] at h
  have spec := (modelRangeMatrix_realize _ _ _).mp (h.mpr (source.countableGraph_range f))
  rw [source.countableGraph_image target j f] at spec
  apply Subtype.ext
  apply ZFSet.ext
  intro y
  constructor
  · intro hy
    obtain ⟨x, edge⟩ := (spec (target.model.member _ y hy)).mp hy
    obtain ⟨n, value⟩ := ZFSet.mem_range.mp edge
    exact ZFSet.mem_range.mpr ⟨n, (ZFSet.pair_inj.mp value).2⟩
  · intro hy
    obtain ⟨n, rfl⟩ := ZFSet.mem_range.mp hy
    exact (j.mem_iff (f n) (source.countableRange f)).mpr (ZFSet.mem_range.mpr ⟨n, rfl⟩)

theorem union_image (x : source.model.Element) : j (source.union x) = target.union (j x) := by
  have sourceSpec : source.model.realize modelUnionMatrix ![x, source.union x] := by
    rw [modelUnionMatrix_realize]
    intro z
    rw [source.union_val, ZFSet.mem_sUnion]
    exact ⟨fun ⟨y, hy, hz⟩ => ⟨source.model.member x y hy, hy, hz⟩,
      fun ⟨y, hy, hz⟩ => ⟨y.val, hy, hz⟩⟩
  have h := j.realize_iff modelUnionMatrix ![x, source.union x]
  have tuple : j ∘ ![x, source.union x] = ![j x, j (source.union x)] := by
    funext i; fin_cases i <;> rfl
  rw [tuple] at h
  have spec := (modelUnionMatrix_realize _ _ _).mp (h.mpr sourceSpec)
  apply target.model.element_ext
  intro z
  rw [target.union_val, ZFSet.mem_sUnion, spec]
  exact ⟨fun ⟨y, hy, hz⟩ => ⟨y.val, hy, hz⟩,
    fun ⟨y, hy, hz⟩ => ⟨target.model.member (j x) y hy, hy, hz⟩⟩

noncomputable def countableUnion (stage : ModelStage.{u}) (f : Nat → stage.model.Element) :
    stage.model.Element := stage.union (stage.countableRange f)

theorem countableUnion_image (f : Nat → source.model.Element) :
    j (source.countableUnion f) = target.countableUnion (j ∘ f) := by
  rw [countableUnion, source.union_image target j, source.countableRange_image target j]
  rfl

end ModelStage
end IBLP
