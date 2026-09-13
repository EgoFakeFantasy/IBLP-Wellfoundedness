import IBLP.NativeStrongShape
import IBLP.Realization.RowGeometry
import FullMarkedBLP.NativeMarks

namespace IBLP

theorem Row.properMark_of_index {row : Row} {owner mark k : Nat}
    (last : row.columns.getLast? = some owner) (below : mark < owner)
    (entry : row.columns[k]? = some mark) (sourcePositive : row.step + 1 ≤ k) : row.ProperMark mark := by
  obtain ⟨bound, value⟩ := List.getElem?_eq_some_iff.mp entry
  refine ⟨k, entry, sourcePositive, ?_⟩
  by_contra notBefore
  have finalIndex : k = row.columns.length - 1 := by omega
  rw [List.getLast?_eq_getElem?, ← finalIndex, entry] at last
  exact below.ne (Option.some.inj last)

namespace NativeBridge

theorem decoded_basic_of_proper {row : FullMarkedBLP.Row} {owner : Nat} (valid : row.CoreValid owner)
    (proper : ∀ mark ∈ row.marks, (decodeRow row).ProperMark mark) : (decodeRow row).BasicValid owner := by
  refine ⟨valid.1, valid.2.1, valid.2.2.1, ?_⟩
  intro mark member
  obtain ⟨k, entry, _⟩ := proper mark member
  exact List.mem_of_getElem? entry

/-- The original positive source-position condition survives one ordinary
or exceptional descent. The generated top has distinct marks, so erasing
the new owner removes that mark completely. No ordering of the parent's
unmodified mark list is assumed by this statement. -/
theorem lower_strong_proper {row lower : FullMarkedBLP.Row} {owner : Nat} {medium : Bool}
    (valid : row.CoreValid owner) (eligible : row.core.length ≤ 2 * row.step)
    (lowerValid : lower.CoreValid (owner - 1)) (distinct : row.marks.Nodup)
    (proper : ∀ mark ∈ row.marks, (decodeRow row).ProperMark mark)
    (run : FullMarkedBLP.nativeLower row owner medium = some lower) :
    ∀ mark ∈ lower.marks, (decodeRow lower).ProperMark mark := by
  have oldValid := decoded_basic_of_proper valid proper
  cases medium with
  | true =>
    cases Option.some.inj run
    intro mark member
    have kept := distinct.mem_erase_iff.mp member
    have oldProper := proper mark kept.2
    have oldBelow := Row.properMark_lt oldValid oldProper
    obtain ⟨k, entry, positive, _⟩ := oldProper
    have retained := FullMarkedBLP.erase_greater_preserves_index valid.1 entry oldBelow
    exact Row.properMark_of_index lowerValid.2.2.1 (by omega) retained positive
  | false =>
    obtain ⟨source, he, out⟩ := Option.bind_eq_some_iff.mp run
    cases Option.some.inj out
    intro mark member
    have kept := distinct.mem_erase_iff.mp member
    have oldProper := proper mark kept.2
    have oldBelow := Row.properMark_lt oldValid oldProper
    obtain ⟨k, entry, positive, _⟩ := oldProper
    have retained := FullMarkedBLP.erase_greater_preserves_index valid.1 entry oldBelow
    have stepPositive := valid.2.2.2.1
    have stepRoom := FullMarkedBLP.Row.step_lt_length valid.2.2.2
    have sourceAt : row.core[row.core.length - row.step]? = some source := by
      simpa only [FullMarkedBLP.Row.e, FullMarkedBLP.fromRight,
        show 0 < row.step ∧ row.step ≤ row.core.length by omega, if_true] using he
    obtain ⟨sourceBound, sourceValue⟩ := List.getElem?_eq_some_iff.mp sourceAt
    obtain ⟨markBound, markValue⟩ := List.getElem?_eq_some_iff.mp entry
    change row.core[k] = mark at markValue
    have sourceBelow := List.pairwise_iff_getElem.mp valid.1 (row.core.length - row.step) k
      sourceBound markBound (by change row.step + 1 ≤ k at positive; omega)
    rw [sourceValue, markValue] at sourceBelow
    obtain ⟨j, indexBound, atNew⟩ := FullMarkedBLP.erase_index_bound retained sourceBelow.ne'
    exact Row.properMark_of_index lowerValid.2.2.1 (by omega) atNew
      (by change row.step - 1 + 1 ≤ j; change row.step + 1 ≤ k at positive; omega)

end NativeBridge
end IBLP
