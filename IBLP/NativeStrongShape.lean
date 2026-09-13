import IBLP.NativeTotal
import FullMarkedBLP.NativeClosure

/-! The short/medium descent inductions follow the fixed upstream native
array proofs (Apache-2.0), with the conclusion strengthened to the original
IBLP three shape alternatives. All declarations are rechecked here. -/
namespace IBLP.NativeBridge

theorem decoded_short_shape {row : FullMarkedBLP.Row} (length : row.core.length + 1 = 2 * row.step)
    (step : 3 ≤ row.step) : (decodeRow row).OrdinaryShape := by
  right; right
  change row.core.length = 2 * row.step - 1 ∧ 3 ≤ row.step
  exact ⟨by omega, step⟩

theorem short_block_shapes (k : Nat) {base : Nat} {top : FullMarkedBLP.Row} {block : FullMarkedBLP.Pattern}
    (valid : top.CoreValid (base + k)) (length : top.core.length + 1 = 2 * top.step)
    (step : k + 3 ≤ top.step) (targets : ∀ x, base ≤ x → x ≤ base + k → x ∈ top.core)
    (run : FullMarkedBLP.nativeBlockDown k (base + k) false top = some block) :
    ∀ row ∈ block, (decodeRow row).OrdinaryShape := by
  induction k generalizing top block with
  | zero =>
    cases Option.some.inj run
    intro row member
    have same := List.mem_singleton.mp member
    subst row
    exact decoded_short_shape length (by omega)
  | succ k ih =>
    obtain ⟨lower, lowerStep, run⟩ := Option.bind_eq_some_iff.mp run
    obtain ⟨earlier, earlierRun, out⟩ := Option.bind_eq_some_iff.mp run
    cases Option.some.inj out
    have previous : base + (k + 1) - 1 = base + k := by omega
    have member := targets (base + (k + 1) - 1) (by omega) (by omega)
    have lowerValid := FullMarkedBLP.nativeLower_short_coreValid valid member (by omega) (by omega) length lowerStep
    rw [previous] at lowerValid earlierRun
    have lowerLength := (FullMarkedBLP.nativeLower_short_shape valid (by omega) length lowerStep).2
    have lowerStepEq := FullMarkedBLP.nativeLower_step lowerStep
    simp only [Bool.false_eq_true, if_false] at lowerStepEq
    have retained := FullMarkedBLP.nativeLower_preserves_targets valid targets (by omega) lowerStep
    have earlierShapes := ih lowerValid lowerLength (by omega)
      (fun x lo hi => retained x lo (by omega)) earlierRun
    intro row member
    rcases List.mem_append.mp member with old | last
    · exact earlierShapes row old
    · have same := List.mem_singleton.mp last
      subst row
      exact decoded_short_shape length (by omega)

theorem medium_block_shapes (k : Nat) {base : Nat} {top : FullMarkedBLP.Row} {block : FullMarkedBLP.Pattern}
    (valid : top.CoreValid (base + (k + 1))) (length : top.core.length = 2 * top.step)
    (step : k + 3 ≤ top.step) (targets : ∀ x, base ≤ x → x ≤ base + (k + 1) → x ∈ top.core)
    (run : FullMarkedBLP.nativeBlockDown (k + 1) (base + (k + 1)) true top = some block) :
    ∀ row ∈ block, (decodeRow row).OrdinaryShape := by
  let lower : FullMarkedBLP.Row := ⟨top.core.erase (base + (k + 1)), top.step,
    top.marks.erase (base + (k + 1) - 1)⟩
  have lowerStep : FullMarkedBLP.nativeLower top (base + (k + 1)) true = some lower := rfl
  obtain ⟨earlier, earlierRun, out⟩ := Option.bind_eq_some_iff.mp run
  cases Option.some.inj out
  have previous : base + (k + 1) - 1 = base + k := by omega
  have member := targets (base + (k + 1) - 1) (by omega) (by omega)
  have lowerValid := FullMarkedBLP.nativeLower_medium_coreValid valid member (by omega) (by omega) length lowerStep
  rw [previous] at lowerValid earlierRun
  have lowerLength := (FullMarkedBLP.nativeLower_medium_shape (List.mem_of_getLast? valid.2.2.1)
    (by omega) length lowerStep).2
  have lowerStepEq := FullMarkedBLP.nativeLower_step lowerStep
  simp only [Bool.true_eq, if_true] at lowerStepEq
  have lowerDescription : lower = ⟨top.core.erase (base + (k + 1)), top.step,
      top.marks.erase (base + (k + 1) - 1)⟩ := (Option.some.inj lowerStep).symm
  have earlierShapes := short_block_shapes k lowerValid lowerLength (by omega)
    (fun x lo hi => by
      rw [lowerDescription]
      exact (List.mem_erase_of_ne (by omega)).mpr (targets x lo (by omega))) earlierRun
  intro row member
  rcases List.mem_append.mp member with old | last
  · exact earlierShapes row old
  · have same := List.mem_singleton.mp last
    subst row
    right; left
    exact ⟨length, by change 1 ≤ top.step; omega⟩

end IBLP.NativeBridge

namespace IBLP

theorem nativeBlock_shapes {a : Pattern} (valid : BasicValid a) (shapes : OrdinaryShape a)
    {r : Nat} {row : Row} {sources : List Nat} {block : Pattern}
    (hr : rowAt a r = some row) (sourcesRun : nativeSources a r = some sources)
    (run : nativeBlock row r sources = some block) : ∀ out ∈ block, out.OrdinaryShape := by
  have encodedValid := NativeBridge.valid_encode valid shapes
  have encodedRow : FullMarkedBLP.rowAt (NativeBridge.encode a) r = some (NativeBridge.encodeRow row) := by
    simp only [NativeBridge.rowAt_encode, hr, Option.map_some]
  have encodedSources := (NativeBridge.nativeSources_encode a r).trans sourcesRun
  have encodedBlock : FullMarkedBLP.nativeBlock (NativeBridge.encodeRow row) r sources = some (NativeBridge.encode block) := by
    rw [NativeBridge.nativeBlock_encode, run]
    rfl
  have hv := encodedValid _ _ encodedRow
  cases sources with
  | nil =>
    have same : block = [row] := (Option.some.inj run).symm
    intro out member
    rw [same] at member
    have eq := List.mem_singleton.mp member
    subst out
    exact shapes row (rowAt_mem hr)
  | cons s ss =>
    have nonempty : s :: ss ≠ [] := by simp
    have eligible := FullMarkedBLP.nativeSources_nonempty_eligible encodedRow encodedSources nonempty
    have minStep := FullMarkedBLP.nativeSources_nonempty_step_ge_two hv encodedRow encodedSources nonempty
    change 2 ≤ row.step at minStep
    have topValid := FullMarkedBLP.nativeTop_actual_coreValid encodedValid encodedRow encodedSources
    have topLength := FullMarkedBLP.nativeTop_actual_length encodedValid encodedRow encodedSources
    have targets := FullMarkedBLP.nativeTop_contains_targets hv (s :: ss)
    have allShapes : ∀ out ∈ NativeBridge.encode block, (NativeBridge.decodeRow out).OrdinaryShape := by
      by_cases medium : row.columns.length = 2 * row.step
      · apply NativeBridge.medium_block_shapes ss.length topValid
          (by change _ = 2 * (row.step + (s :: ss).length); change _ = row.columns.length + 2 * (s :: ss).length at topLength; omega)
          (by change _ ≤ row.step + (s :: ss).length; simp; omega) targets
        simpa only [FullMarkedBLP.nativeBlock, List.isEmpty_cons, Bool.false_eq_true, if_false,
          NativeBridge.encode_columns, NativeBridge.encode_step, medium, beq_self_eq_true] using encodedBlock
      · have short := FullMarkedBLP.Row.short_shape_of_eligible_ne_medium hv.2.2.2 eligible medium
        change row.columns.length + 1 = 2 * row.step ∧ 3 ≤ row.step at short
        apply NativeBridge.short_block_shapes (s :: ss).length topValid
          (by change _ + 1 = 2 * (row.step + (s :: ss).length); change _ = row.columns.length + 2 * (s :: ss).length at topLength; omega)
          (by change _ ≤ row.step + (s :: ss).length; have := short.2; change 3 ≤ row.step at this; omega) targets
        have notMedium : (row.columns.length == 2 * row.step) = false := by simp [medium]
        simpa only [FullMarkedBLP.nativeBlock, List.isEmpty_cons, Bool.false_eq_true, if_false,
          NativeBridge.encode_columns, NativeBridge.encode_step, notMedium] using encodedBlock
    intro out member
    exact allShapes (NativeBridge.encodeRow out) (List.mem_map.mpr ⟨out, member, rfl⟩)

theorem native_preserves_shapes {a b : Pattern} (valid : BasicValid a) (shapes : OrdinaryShape a)
    {r : Nat} {sources : List Nat} (run : native a r = some (b, sources)) : OrdinaryShape b := by
  obtain ⟨row, hr, rest⟩ := Option.bind_eq_some_iff.mp run
  obtain ⟨ss, sourceRun, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨block, blockRun, out⟩ := Option.bind_eq_some_iff.mp rest
  cases Option.some.inj out
  intro result member
  rcases List.mem_append.mp member with earlier | later
  · rcases List.mem_append.mp earlier with old | family
    · exact shapes result (List.mem_of_mem_take old)
    · exact nativeBlock_shapes valid shapes hr sourceRun blockRun result family
  · obtain ⟨old, oldMember, same⟩ := List.mem_map.mp later
    subst result
    have oldShape := shapes old (List.mem_of_mem_drop oldMember)
    simpa only [Row.OrdinaryShape, Row.shiftAfter, List.length_map] using oldShape

end IBLP
