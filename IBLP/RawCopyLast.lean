import IBLP.RawCopy
import IBLP.Pointers

namespace IBLP

theorem rawCopy_last {a b : Pattern} {last : Row} {p : Nat}
    (copy : rawCopy a = some b) (hlast : a.getLast? = some last) (hp : last.p = some p) :
    ∃ next, b.getLast? = some next ∧ copyRow a last a.length = some next := by
  have nonempty := rowAt_pos (getLast_rowAt hlast)
  have length := rawCopy_length copy hlast hp
  have nextNonempty : 0 < b.length := by omega
  obtain ⟨next, atNext⟩ := rowAt_exists nextNonempty (show b.length ≤ b.length from le_rfl)
  have lastNext : b.getLast? = some next := by
    simpa only [List.getLast?_eq_getElem?, rowAt, if_neg (Nat.ne_of_gt nextNonempty)] using atNext
  obtain ⟨source, _, _, owner, rowCopy⟩ := rawCopy_row_origin copy hlast hp (by omega) atNext
  have same : source = a.length := by omega
  exact ⟨next, lastNext, same ▸ rowCopy⟩

end IBLP
