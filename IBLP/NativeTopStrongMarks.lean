import IBLP.NativeStrongMarks
import FullMarkedBLP.NativeTopMarks

namespace IBLP.NativeBridge

theorem sources_before_strong_mark {a : IBLP.Pattern} (valid : IBLP.BasicValid a) (shapes : IBLP.OrdinaryShape a)
    {r mark : Nat} {row : IBLP.Row} {sources : List Nat} (hr : IBLP.rowAt a r = some row)
    (run : IBLP.nativeSources a r = some sources) (proper : row.ProperMark mark) :
    ∀ x ∈ sources, x < mark := by
  have encodedRow : FullMarkedBLP.rowAt (encode a) r = some (encodeRow row) := by simp [hr]
  have encodedRun := (nativeSources_encode a r).trans run
  intro x member
  have nonempty : sources ≠ [] := by intro empty; simp [empty] at member
  have eligible := FullMarkedBLP.nativeSources_nonempty_eligible encodedRow encodedRun nonempty
  change row.columns.length ≤ 2 * row.step at eligible
  have shape := shapes row (IBLP.rowAt_mem hr)
  obtain ⟨p, hp⟩ := IBLP.fromRight_exists (xs := row.columns) (k := row.step + 1)
    (by omega) (by have := IBLP.Row.step_lt_length shape; omega)
  obtain ⟨e, he⟩ := IBLP.fromRight_exists (xs := row.columns) (k := row.step)
    (IBLP.Row.step_pos shape) (IBLP.Row.step_lt_length shape).le
  have sourceBound := FullMarkedBLP.nativeSources_between (valid_encode valid shapes) encodedRow hp he encodedRun x member
  obtain ⟨k, atMark, positive, _⟩ := proper
  have atEndpoint : row.columns[row.columns.length - row.step]? = some e := by
    simpa only [IBLP.fromRight, show 0 < row.step ∧ row.step ≤ row.columns.length by
      have := IBLP.Row.step_pos shape; have := IBLP.Row.step_lt_length shape; omega, if_true] using he
  obtain ⟨eb, ev⟩ := List.getElem?_eq_some_iff.mp atEndpoint
  obtain ⟨mb, mv⟩ := List.getElem?_eq_some_iff.mp atMark
  have before := List.pairwise_iff_getElem.mp (valid _ _ hr).1 (row.columns.length - row.step) k eb mb (by omega)
  rw [ev, mv] at before
  exact sourceBound.2.trans before

/-- Every actual native-top mark has a strictly positive paired source
position. The top's own canonicalization supplies distinct/sorted marks;
the old mark list need not already be canonical. -/
theorem top_strong_proper {a : IBLP.Pattern} (valid : IBLP.BasicValid a) (shapes : IBLP.OrdinaryShape a)
    {r : Nat} {row : IBLP.Row} {sources : List Nat} (hr : IBLP.rowAt a r = some row)
    (run : IBLP.nativeSources a r = some sources)
    (proper : ∀ mark ∈ row.marks, row.ProperMark mark) :
    ∀ mark ∈ (FullMarkedBLP.nativeTop (encodeRow row) r sources).marks,
      (decodeRow (FullMarkedBLP.nativeTop (encodeRow row) r sources)).ProperMark mark := by
  have encodedValid := valid_encode valid shapes
  have encodedRow : FullMarkedBLP.rowAt (encode a) r = some (encodeRow row) := by simp [hr]
  have encodedRun := (nativeSources_encode a r).trans run
  have hv := valid _ _ hr
  have topValid := FullMarkedBLP.nativeTop_actual_coreValid encodedValid encodedRow encodedRun
  have oldBelow : ∀ mark ∈ (encodeRow row).marks, mark < r :=
    fun mark member => IBLP.Row.properMark_lt hv (proper mark member)
  intro mark member
  have below := FullMarkedBLP.nativeTop_marks_before_owner oldBelow mark member
  have inCore := FullMarkedBLP.nativeTop_marks_in_core hv.2.2.2 (List.mem_of_getLast? hv.2.2.1) mark member
  obtain ⟨k, entry⟩ := List.mem_iff_getElem?.mp inCore
  have rankEq := FullMarkedBLP.sorted_rank_at_index topValid.1 entry
  apply IBLP.Row.properMark_of_index topValid.2.2.1 below entry
  change row.step + sources.length + 1 ≤ k
  have origin := member
  simp only [FullMarkedBLP.nativeTop, FullMarkedBLP.mem_canonicalColumns, List.mem_filter,
    List.mem_append, List.mem_map, List.mem_range] at origin
  rcases origin.1 with old | ⟨i, ib, value⟩
  · obtain ⟨j, oldEntry, oldPositive, _⟩ := proper mark old
    have rankOld := FullMarkedBLP.sorted_rank_at_index hv.1 oldEntry
    have bound := FullMarkedBLP.nativeTop_rank_bound encodedValid encodedRow encodedRun
      (sources_before_strong_mark valid shapes hr run (proper mark old))
    change (row.columns.filter (· < mark)).length + sources.length ≤ _ at bound
    omega
  · have nonempty : sources ≠ [] := by intro empty; simp [empty] at ib
    have minStep := FullMarkedBLP.nativeSources_nonempty_step_ge_two (encodedValid _ _ encodedRow) encodedRow encodedRun nonempty
    change 2 ≤ row.step at minStep
    have shape := shapes row (IBLP.rowAt_mem hr)
    have room : row.step + 2 ≤ row.columns.length := by
      rcases shape with shape | shape | shape <;> omega
    have ownerLe : r ≤ mark := by omega
    have sourcesBelow := FullMarkedBLP.nativeSources_below_owner encodedValid encodedRow encodedRun
    have bound := FullMarkedBLP.nativeTop_rank_bound encodedValid encodedRow encodedRun
      (fun x hx => (sourcesBelow x hx).trans_le ownerLe)
    change (row.columns.filter (· < mark)).length + sources.length ≤ _ at bound
    have oldRank := FullMarkedBLP.sorted_rank_at_index hv.1
      (show row.columns[row.columns.length - 1]? = some r by simpa only [← List.getLast?_eq_getElem?] using hv.2.2.1)
    have subset : ∀ x ∈ row.columns.filter (· < r), x ∈ row.columns.filter (· < mark) := by
      intro x member
      have hx := List.mem_filter.mp member
      exact List.mem_filter.mpr ⟨hx.1, by simp only [decide_eq_true_eq] at hx ⊢; omega⟩
    have count := FullMarkedBLP.nodup_subset_length
      ((hv.1.imp (fun h => Nat.ne_of_lt h)).sublist List.filter_sublist) subset
    omega

end IBLP.NativeBridge
