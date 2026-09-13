import IBLP.NativeMinimum
import FullMarkedBLP.RowTraces

/-! The descent induction follows the fixed upstream native trace
induction (Apache-2.0), retaining an arbitrary property of the actual
marked target/source pair. This keeps later semantic certificates intact. -/
namespace IBLP.NativeBridge

def MarkPairs (P : Nat → Nat → Prop) (row : FullMarkedBLP.Row) : Prop :=
  ∀ mark ∈ row.marks, ∃ k source, row.step ≤ k ∧ row.core[k]? = some mark ∧
    row.core[k - row.step]? = some source ∧ P mark source

theorem lower_medium_markPairs {P : Nat → Nat → Prop} {row lower : FullMarkedBLP.Row} {owner : Nat}
    (valid : row.CoreValid owner) (proper : row.ProperMarks owner) (data : MarkPairs P row)
    (run : FullMarkedBLP.nativeLower row owner true = some lower) : MarkPairs P lower := by
  intro mark member
  have oldMember := (FullMarkedBLP.nativeLower_marks_sublist run).subset member
  obtain ⟨k, source, index, targetAt, sourceAt, payload⟩ := data mark oldMember
  have pair := FullMarkedBLP.nativeLower_medium_pair valid (proper.2 mark oldMember).1 targetAt sourceAt run
  have step := FullMarkedBLP.nativeLower_step run
  simp only [if_true] at step
  exact ⟨k, source, by omega, pair.1, pair.2, payload⟩

theorem lower_short_markPairs {P : Nat → Nat → Prop} {row lower : FullMarkedBLP.Row} {owner : Nat}
    (valid : row.CoreValid owner) (proper : row.ProperMarks owner) (length : row.core.length + 1 = 2 * row.step)
    (data : MarkPairs P row) (run : FullMarkedBLP.nativeLower row owner false = some lower) : MarkPairs P lower := by
  intro mark member
  have oldMember := (FullMarkedBLP.nativeLower_marks_sublist run).subset member
  obtain ⟨k, source, index, targetAt, sourceAt, payload⟩ := data mark oldMember
  have pair := FullMarkedBLP.nativeLower_short_pair valid proper length oldMember index targetAt sourceAt run
  have step := FullMarkedBLP.nativeLower_step run
  simp only [Bool.false_eq_true, if_false] at step
  exact ⟨k - 1, source, by omega, pair.1, pair.2, payload⟩

theorem short_block_markPairs (P : Nat → Nat → Prop) (k : Nat)
    {base : Nat} {top : FullMarkedBLP.Row} {block : FullMarkedBLP.Pattern}
    (valid : top.CoreValid (base + k)) (proper : top.ProperMarks (base + k))
    (length : top.core.length + 1 = 2 * top.step) (step : k + 3 ≤ top.step)
    (targets : ∀ x, base ≤ x → x ≤ base + k → x ∈ top.core) (data : MarkPairs P top)
    (run : FullMarkedBLP.nativeBlockDown k (base + k) false top = some block) :
    ∀ out ∈ block, MarkPairs P out := by
  induction k generalizing top block with
  | zero =>
    cases Option.some.inj run
    intro out member
    have same := List.mem_singleton.mp member
    subst out
    exact data
  | succ k ih =>
    obtain ⟨lower, lowerRun, rest⟩ := Option.bind_eq_some_iff.mp run
    obtain ⟨earlier, earlierRun, out⟩ := Option.bind_eq_some_iff.mp rest
    cases Option.some.inj out
    have previous : base + (k + 1) - 1 = base + k := by omega
    have member := targets (base + (k + 1) - 1) (by omega) (by omega)
    have lowerValid := FullMarkedBLP.nativeLower_short_coreValid valid member (by omega) (by omega) length lowerRun
    have lowerProper := FullMarkedBLP.nativeLower_short_proper valid proper length lowerRun
    rw [previous] at lowerValid lowerProper earlierRun
    have lowerLength := (FullMarkedBLP.nativeLower_short_shape valid (by omega) length lowerRun).2
    have lowerStep := FullMarkedBLP.nativeLower_step lowerRun
    simp only [Bool.false_eq_true, if_false] at lowerStep
    have retained := FullMarkedBLP.nativeLower_preserves_targets valid targets (by omega) lowerRun
    have allPairs := ih lowerValid lowerProper lowerLength (by omega)
      (fun x lo hi => retained x lo (by omega)) (lower_short_markPairs valid proper length data lowerRun) earlierRun
    intro out member
    rcases List.mem_append.mp member with old | last
    · exact allPairs out old
    · have same := List.mem_singleton.mp last
      subst out
      exact data

theorem medium_block_markPairs (P : Nat → Nat → Prop) (k : Nat)
    {base : Nat} {top : FullMarkedBLP.Row} {block : FullMarkedBLP.Pattern}
    (valid : top.CoreValid (base + (k + 1))) (proper : top.ProperMarks (base + (k + 1)))
    (length : top.core.length = 2 * top.step) (step : k + 3 ≤ top.step)
    (targets : ∀ x, base ≤ x → x ≤ base + (k + 1) → x ∈ top.core) (data : MarkPairs P top)
    (run : FullMarkedBLP.nativeBlockDown (k + 1) (base + (k + 1)) true top = some block) :
    ∀ out ∈ block, MarkPairs P out := by
  let lower : FullMarkedBLP.Row := ⟨top.core.erase (base + (k + 1)), top.step,
    top.marks.erase (base + (k + 1) - 1)⟩
  have lowerRun : FullMarkedBLP.nativeLower top (base + (k + 1)) true = some lower := rfl
  obtain ⟨earlier, earlierRun, out⟩ := Option.bind_eq_some_iff.mp run
  cases Option.some.inj out
  have previous : base + (k + 1) - 1 = base + k := by omega
  have member := targets (base + (k + 1) - 1) (by omega) (by omega)
  have lowerValid := FullMarkedBLP.nativeLower_medium_coreValid valid member (by omega) (by omega) length lowerRun
  have lowerProper := FullMarkedBLP.nativeLower_medium_proper valid proper lowerRun
  rw [previous] at lowerValid lowerProper earlierRun
  have lowerLength := (FullMarkedBLP.nativeLower_medium_shape (List.mem_of_getLast? valid.2.2.1)
    (by omega) length lowerRun).2
  have lowerStep := FullMarkedBLP.nativeLower_step lowerRun
  simp only [if_true] at lowerStep
  have allPairs := short_block_markPairs P k lowerValid lowerProper lowerLength (by omega)
    (fun x lo hi => (List.mem_erase_of_ne (by omega)).mpr (targets x lo (by omega)))
    (lower_medium_markPairs valid proper data lowerRun) earlierRun
  intro out member
  rcases List.mem_append.mp member with old | last
  · exact allPairs out old
  · have same := List.mem_singleton.mp last
    subst out
    exact data

end IBLP.NativeBridge

namespace IBLP

theorem nativeBlock_markPairs (P : Nat → Nat → Prop) {a : Pattern} (valid : BasicValid a) (shapes : OrdinaryShape a)
    {r : Nat} {row : Row} {sources : List Nat} {block : Pattern}
    (hr : rowAt a r = some row) (sourcesRun : nativeSources a r = some sources)
    (proper : ∀ mark ∈ row.marks, row.ProperMark mark) (run : nativeBlock row r sources = some block)
    (oldData : NativeBridge.MarkPairs P (NativeBridge.encodeRow row))
    (topData : NativeBridge.MarkPairs P (FullMarkedBLP.nativeTop (NativeBridge.encodeRow row) r sources)) :
    ∀ out ∈ block, NativeBridge.MarkPairs P (NativeBridge.encodeRow out) := by
  have encodedValid := NativeBridge.valid_encode valid shapes
  have encodedRow : FullMarkedBLP.rowAt (NativeBridge.encode a) r = some (NativeBridge.encodeRow row) := by simp [hr]
  have encodedSources := (NativeBridge.nativeSources_encode a r).trans sourcesRun
  have encodedBlock := NativeBridge.encoded_block run
  have hv := encodedValid _ _ encodedRow
  cases sources with
  | nil =>
    have same : block = [row] := (Option.some.inj run).symm
    intro out member
    rw [same] at member
    have eq := List.mem_singleton.mp member
    subst out
    exact oldData
  | cons s ss =>
    have nonempty : s :: ss ≠ [] := by simp
    have eligible := FullMarkedBLP.nativeSources_nonempty_eligible encodedRow encodedSources nonempty
    have minStep := FullMarkedBLP.nativeSources_nonempty_step_ge_two hv encodedRow encodedSources nonempty
    change 2 ≤ row.step at minStep
    have topValid := FullMarkedBLP.nativeTop_actual_coreValid encodedValid encodedRow encodedSources
    have topLength := FullMarkedBLP.nativeTop_actual_length encodedValid encodedRow encodedSources
    have targets := FullMarkedBLP.nativeTop_contains_targets hv (s :: ss)
    have topProper := NativeBridge.top_weak_proper valid shapes hr sourcesRun proper
    have allPairs : ∀ out ∈ NativeBridge.encode block, NativeBridge.MarkPairs P out := by
      by_cases medium : row.columns.length = 2 * row.step
      · apply NativeBridge.medium_block_markPairs P ss.length topValid topProper
          (by change _ = 2 * (row.step + (s :: ss).length); change _ = row.columns.length + 2 * (s :: ss).length at topLength; omega)
          (by change _ ≤ row.step + (s :: ss).length; simp; omega) targets topData
        simpa only [FullMarkedBLP.nativeBlock, List.isEmpty_cons, Bool.false_eq_true, if_false,
          NativeBridge.encode_columns, NativeBridge.encode_step, medium, beq_self_eq_true] using encodedBlock
      · have short := FullMarkedBLP.Row.short_shape_of_eligible_ne_medium hv.2.2.2 eligible medium
        change row.columns.length + 1 = 2 * row.step ∧ 3 ≤ row.step at short
        apply NativeBridge.short_block_markPairs P (s :: ss).length topValid topProper
          (by change _ + 1 = 2 * (row.step + (s :: ss).length); change _ = row.columns.length + 2 * (s :: ss).length at topLength; omega)
          (by change _ ≤ row.step + (s :: ss).length; omega) targets topData
        have notMedium : (row.columns.length == 2 * row.step) = false := by simp [medium]
        simpa only [FullMarkedBLP.nativeBlock, List.isEmpty_cons, Bool.false_eq_true, if_false,
          NativeBridge.encode_columns, NativeBridge.encode_step, notMedium] using encodedBlock
    intro out member
    exact allPairs (NativeBridge.encodeRow out) (List.mem_map.mpr ⟨out, member, rfl⟩)

end IBLP
