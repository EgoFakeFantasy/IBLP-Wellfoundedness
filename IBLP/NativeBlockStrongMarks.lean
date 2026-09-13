import IBLP.NativeTopStrongMarks

namespace IBLP.NativeBridge

theorem lower_marks_nodup {row lower : FullMarkedBLP.Row} {owner : Nat} {medium : Bool}
    (distinct : row.marks.Nodup) (run : FullMarkedBLP.nativeLower row owner medium = some lower) :
    lower.marks.Nodup := by
  cases medium with
  | true => cases Option.some.inj run; exact distinct.sublist List.erase_sublist
  | false =>
    obtain ⟨source, _, out⟩ := Option.bind_eq_some_iff.mp run
    cases Option.some.inj out
    exact distinct.sublist List.erase_sublist

theorem short_block_strong_proper (k : Nat) {base : Nat} {top : FullMarkedBLP.Row} {block : FullMarkedBLP.Pattern}
    (valid : top.CoreValid (base + k)) (length : top.core.length + 1 = 2 * top.step)
    (step : k + 3 ≤ top.step) (targets : ∀ x, base ≤ x → x ≤ base + k → x ∈ top.core)
    (distinct : top.marks.Nodup) (proper : ∀ mark ∈ top.marks, (decodeRow top).ProperMark mark)
    (run : FullMarkedBLP.nativeBlockDown k (base + k) false top = some block) :
    ∀ row ∈ block, ∀ mark ∈ row.marks, (decodeRow row).ProperMark mark := by
  induction k generalizing top block with
  | zero =>
    cases Option.some.inj run
    intro row member
    have same := List.mem_singleton.mp member
    subst row
    exact proper
  | succ k ih =>
    obtain ⟨lower, lowerStep, run⟩ := Option.bind_eq_some_iff.mp run
    obtain ⟨earlier, earlierRun, out⟩ := Option.bind_eq_some_iff.mp run
    cases Option.some.inj out
    have previous : base + (k + 1) - 1 = base + k := by omega
    have member := targets (base + (k + 1) - 1) (by omega) (by omega)
    have lowerValid := FullMarkedBLP.nativeLower_short_coreValid valid member (by omega) (by omega) length lowerStep
    have lowerProper := lower_strong_proper valid (by omega) lowerValid distinct proper lowerStep
    rw [previous] at lowerValid earlierRun
    have lowerLength := (FullMarkedBLP.nativeLower_short_shape valid (by omega) length lowerStep).2
    have lowerStepEq := FullMarkedBLP.nativeLower_step lowerStep
    simp only [Bool.false_eq_true, if_false] at lowerStepEq
    have retained := FullMarkedBLP.nativeLower_preserves_targets valid targets (by omega) lowerStep
    have earlierProper := ih lowerValid lowerLength (by omega)
      (fun x lo hi => retained x lo (by omega)) (lower_marks_nodup distinct lowerStep) lowerProper earlierRun
    intro row member
    rcases List.mem_append.mp member with old | last
    · exact earlierProper row old
    · have same := List.mem_singleton.mp last
      subst row
      exact proper

theorem medium_block_strong_proper (k : Nat) {base : Nat} {top : FullMarkedBLP.Row} {block : FullMarkedBLP.Pattern}
    (valid : top.CoreValid (base + (k + 1))) (length : top.core.length = 2 * top.step)
    (step : k + 3 ≤ top.step) (targets : ∀ x, base ≤ x → x ≤ base + (k + 1) → x ∈ top.core)
    (distinct : top.marks.Nodup) (proper : ∀ mark ∈ top.marks, (decodeRow top).ProperMark mark)
    (run : FullMarkedBLP.nativeBlockDown (k + 1) (base + (k + 1)) true top = some block) :
    ∀ row ∈ block, ∀ mark ∈ row.marks, (decodeRow row).ProperMark mark := by
  let lower : FullMarkedBLP.Row := ⟨top.core.erase (base + (k + 1)), top.step,
    top.marks.erase (base + (k + 1) - 1)⟩
  have lowerStep : FullMarkedBLP.nativeLower top (base + (k + 1)) true = some lower := rfl
  obtain ⟨earlier, earlierRun, out⟩ := Option.bind_eq_some_iff.mp run
  cases Option.some.inj out
  have previous : base + (k + 1) - 1 = base + k := by omega
  have member := targets (base + (k + 1) - 1) (by omega) (by omega)
  have lowerValid := FullMarkedBLP.nativeLower_medium_coreValid valid member (by omega) (by omega) length lowerStep
  have lowerProper := lower_strong_proper valid (by omega) lowerValid distinct proper lowerStep
  rw [previous] at lowerValid earlierRun
  have lowerLength := (FullMarkedBLP.nativeLower_medium_shape (List.mem_of_getLast? valid.2.2.1)
    (by omega) length lowerStep).2
  have lowerStepEq := FullMarkedBLP.nativeLower_step lowerStep
  simp only [if_true] at lowerStepEq
  have earlierProper := short_block_strong_proper k lowerValid lowerLength (by omega)
    (fun x lo hi => (List.mem_erase_of_ne (by omega)).mpr (targets x lo (by omega)))
    (lower_marks_nodup distinct lowerStep) lowerProper earlierRun
  intro row member
  rcases List.mem_append.mp member with old | last
  · exact earlierProper row old
  · have same := List.mem_singleton.mp last
    subst row
    exact proper

end IBLP.NativeBridge

namespace IBLP

theorem nativeBlock_proper {a : Pattern} (valid : BasicValid a) (shapes : OrdinaryShape a)
    {r : Nat} {row : Row} {sources : List Nat} {block : Pattern}
    (hr : rowAt a r = some row) (sourcesRun : nativeSources a r = some sources)
    (proper : ∀ mark ∈ row.marks, row.ProperMark mark)
    (run : nativeBlock row r sources = some block) : ∀ out ∈ block, ∀ mark ∈ out.marks, out.ProperMark mark := by
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
    exact proper
  | cons s ss =>
    have nonempty : s :: ss ≠ [] := by simp
    have eligible := FullMarkedBLP.nativeSources_nonempty_eligible encodedRow encodedSources nonempty
    have minStep := FullMarkedBLP.nativeSources_nonempty_step_ge_two hv encodedRow encodedSources nonempty
    change 2 ≤ row.step at minStep
    have topValid := FullMarkedBLP.nativeTop_actual_coreValid encodedValid encodedRow encodedSources
    have topLength := FullMarkedBLP.nativeTop_actual_length encodedValid encodedRow encodedSources
    have targets := FullMarkedBLP.nativeTop_contains_targets hv (s :: ss)
    have topProper := NativeBridge.top_strong_proper valid shapes hr sourcesRun proper
    have topDistinct := (FullMarkedBLP.nativeTop_sorted (NativeBridge.encodeRow row) r (s :: ss)).2.imp
      (fun h => Nat.ne_of_lt h)
    have allProper : ∀ out ∈ NativeBridge.encode block, ∀ mark ∈ out.marks, (NativeBridge.decodeRow out).ProperMark mark := by
      by_cases medium : row.columns.length = 2 * row.step
      · apply NativeBridge.medium_block_strong_proper ss.length topValid
          (by change _ = 2 * (row.step + (s :: ss).length); change _ = row.columns.length + 2 * (s :: ss).length at topLength; omega)
          (by change _ ≤ row.step + (s :: ss).length; simp; omega) targets topDistinct topProper
        simpa only [FullMarkedBLP.nativeBlock, List.isEmpty_cons, Bool.false_eq_true, if_false,
          NativeBridge.encode_columns, NativeBridge.encode_step, medium, beq_self_eq_true] using encodedBlock
      · have short := FullMarkedBLP.Row.short_shape_of_eligible_ne_medium hv.2.2.2 eligible medium
        change row.columns.length + 1 = 2 * row.step ∧ 3 ≤ row.step at short
        apply NativeBridge.short_block_strong_proper (s :: ss).length topValid
          (by change _ + 1 = 2 * (row.step + (s :: ss).length); change _ = row.columns.length + 2 * (s :: ss).length at topLength; omega)
          (by change _ ≤ row.step + (s :: ss).length; omega) targets topDistinct topProper
        have notMedium : (row.columns.length == 2 * row.step) = false := by simp [medium]
        simpa only [FullMarkedBLP.nativeBlock, List.isEmpty_cons, Bool.false_eq_true, if_false,
          NativeBridge.encode_columns, NativeBridge.encode_step, notMedium] using encodedBlock
    intro out member
    exact allProper (NativeBridge.encodeRow out) (List.mem_map.mpr ⟨out, member, rfl⟩)

end IBLP
