import IBLP.CompletionStrongClosure
import FullMarkedBLP.CompletionEarlierMark
import FullMarkedBLP.CompletionLaterMark

namespace IBLP.Row.CompletionGeometry

variable {row : Row} {owner mark : Nat} {sources : List Nat}
variable (C : row.CompletionGeometry owner mark sources)
include C

/-- Exact source/target gaps for every old core pair follow already from
the insertion position and the paired source gap. No semantic map or
new mark certificate is required for this old-pair assertion. -/
theorem old_pair_intervals (valid : row.BasicValid owner) (shape : row.OrdinaryShape)
    {k x z : Nat} (legal : row.step ≤ k) (atTarget : row.columns[k]? = some z)
    (atSource : row.columns[k - row.step]? = some x) :
    (x ≤ z ∧ z ≤ mark ∧ ∀ s ∈ sources, x < s ∧ s < z) ∨
      (x ≤ mark ∧ mark + sources.length < z ∧ ∀ s ∈ sources, s < x) := by
  obtain ⟨p, hp⟩ := fromRight_exists (xs := row.columns) (k := row.step + 1)
    (by omega) (by have := Row.step_lt_length shape; omega)
  have core : (NativeBridge.encodeRow row).CoreValid owner :=
    ⟨valid.1, valid.2.1, valid.2.2.1, NativeBridge.shape_encode shape⟩
  have xp := FullMarkedBLP.step_source_le_p core atTarget atSource hp
  have pz := FullMarkedBLP.target_position_after_p core legal atTarget hp
  have pm := FullMarkedBLP.target_position_after_p core
    (Nat.le_trans (Nat.le_succ _) C.positive) C.mark_at hp
  by_cases earlier : k ≤ C.index
  · have left := Row.column_index_le valid.1 atSource C.left_at (by omega)
    have target := Row.column_index_le valid.1 atTarget C.mark_at earlier
    refine Or.inl ⟨by omega, target, ?_⟩
    intro s member
    exact ⟨lt_of_le_of_lt left (C.source_gap s member).1,
      lt_of_lt_of_le (C.sources_below_p valid.1 shape hp s member) pz⟩
  · have right := Row.column_index_le valid.1 C.right_at atSource (by have := C.positive; omega)
    obtain ⟨mkBound, mkValue⟩ := List.getElem?_eq_some_iff.mp C.mark_at
    obtain ⟨zBound, zValue⟩ := List.getElem?_eq_some_iff.mp atTarget
    have above : mark < z := by
      simpa only [mkValue, zValue] using
        List.pairwise_iff_getElem.mp valid.1 C.index k mkBound zBound (by omega)
    have beyond : mark + sources.length < z := by
      by_contra failure
      exact C.target_gap z above (by omega) (List.mem_of_getElem? atTarget)
    exact Or.inr ⟨by omega, beyond,
      fun s member => lt_of_lt_of_le (C.source_gap s member).2 right⟩

/-- Every original source/target pair remains a step-pair in the actual
completed row, including pairs other than the mark being completed. -/
theorem old_core_pairs (valid : row.BasicValid owner) (shape : row.OrdinaryShape)
    {k x z : Nat} (legal : row.step ≤ k) (atTarget : row.columns[k]? = some z)
    (atSource : row.columns[k - row.step]? = some x) :
    ∃ j, (completeMarkRow row mark sources).columns[j]? = some x ∧
      (completeMarkRow row mark sources).columns[j + (completeMarkRow row mark sources).step]? = some z := by
  rcases C.old_pair_intervals valid shape legal atTarget atSource with
    ⟨xz, zm, gap⟩ | ⟨xm, high, below⟩
  · obtain ⟨target, source⟩ := FullMarkedBLP.completeMarkRow_earlier_pair
      (row := NativeBridge.encodeRow row) valid.1 C.distinct (C.disjoint valid.1)
      C.target_gap legal atTarget atSource xz zm gap
    simp only [NativeBridge.completeMarkRow_encode, NativeBridge.encode_columns,
      NativeBridge.encode_step] at target source
    refine ⟨k - row.step, ?_, ?_⟩
    · convert source using 1
      simp only [completeMarkRow]
      congr 1
      omega
    · convert target using 1
      simp only [completeMarkRow]
      congr 1
      omega
  · obtain ⟨target, source⟩ := FullMarkedBLP.completeMarkRow_later_pair
      (row := NativeBridge.encodeRow row) valid.1 C.distinct (C.disjoint valid.1)
      C.target_gap legal atTarget atSource xm below high
    simp only [NativeBridge.completeMarkRow_encode, NativeBridge.encode_columns,
      NativeBridge.encode_step] at target source
    refine ⟨k - row.step + sources.length, ?_, ?_⟩
    · convert source using 1
      simp only [completeMarkRow]
      congr 1
      omega
    · convert target using 1
      simp only [completeMarkRow]
      congr 1
      omega

end IBLP.Row.CompletionGeometry
