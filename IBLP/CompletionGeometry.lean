import IBLP.NativeStrongMarks
import FullMarkedBLP.CompletionMinimum

/-! Exact original row completion. The geometric packet is a local proof
obligation for the event induction, not an extra guard on the program.
Only the identical array operation is translated to the pinned upstream. -/
namespace IBLP

namespace NativeBridge

@[simp] theorem completeMarkRow_encode (row : IBLP.Row) (mark : Nat) (sources : List Nat) :
    FullMarkedBLP.completeMarkRow (encodeRow row) mark sources =
      encodeRow (IBLP.completeMarkRow row mark sources) := by
  simp only [FullMarkedBLP.completeMarkRow, IBLP.completeMarkRow, encodeRow,
    IBLP.canonicalColumns_eq_upstream]

end NativeBridge

/-- The two packets lie in the old paired source gap and in a fresh target
gap. The source position is strictly positive, as required by (2.3). -/
structure Row.CompletionGeometry (row : Row) (owner mark : Nat) (sources : List Nat) where
  index : Nat
  left : Nat
  right : Nat
  positive : row.step + 1 ≤ index
  notLast : index + 1 < row.columns.length
  mark_at : row.columns[index]? = some mark
  left_at : row.columns[index - row.step]? = some left
  right_at : row.columns[index - row.step + 1]? = some right
  distinct : sources.Nodup
  source_gap : ∀ x ∈ sources, left < x ∧ x < right
  target_gap : ∀ x, mark < x → x ≤ mark + sources.length → x ∉ row.columns
  before_owner : mark + sources.length < owner

theorem Row.column_index_le {row : Row} {i j x y : Nat}
    (sorted : row.columns.Pairwise (· < ·)) (hx : row.columns[i]? = some x)
    (hy : row.columns[j]? = some y) (order : i ≤ j) : x ≤ y := by
  rcases order.eq_or_lt with same | less
  · subst j
    exact (Option.some.inj (hx.symm.trans hy)).le
  · obtain ⟨hi, vi⟩ := List.getElem?_eq_some_iff.mp hx
    obtain ⟨hj, vj⟩ := List.getElem?_eq_some_iff.mp hy
    exact le_of_lt (by simpa only [vi, vj] using
      List.pairwise_iff_getElem.mp sorted i j hi hj less)

theorem Row.properMark_above_e {row : Row} {mark e : Nat}
    (sorted : row.columns.Pairwise (· < ·)) (shape : row.OrdinaryShape)
    (proper : row.ProperMark mark) (he : row.e = some e) : e < mark := by
  obtain ⟨k, hk, positive, before⟩ := proper
  have hs := Row.step_pos shape
  have hl := Row.step_lt_length shape
  have atE : row.columns[row.columns.length - row.step]? = some e := by
    simpa only [Row.e, fromRight, show 0 < row.step ∧ row.step ≤ row.columns.length by omega,
      if_true] using he
  have order : row.columns.length - row.step < k := by
    rcases shape with ⟨len, step⟩ | ⟨len, step⟩ | ⟨len, step⟩ <;> omega
  obtain ⟨hi, vi⟩ := List.getElem?_eq_some_iff.mp atE
  obtain ⟨hj, vj⟩ := List.getElem?_eq_some_iff.mp hk
  simpa only [vi, vj] using List.pairwise_iff_getElem.mp sorted _ _ hi hj order

namespace Row.CompletionGeometry

variable {row : Row} {owner mark : Nat} {sources : List Nat}
variable (C : row.CompletionGeometry owner mark sources)
include C

theorem proper : row.ProperMark mark := ⟨C.index, C.mark_at, C.positive, C.notLast⟩

theorem disjoint (sorted : row.columns.Pairwise (· < ·)) :
    ∀ x ∈ sources, x ∉ row.columns := by
  intro x hx
  exact FullMarkedBLP.between_adjacent_not_mem sorted C.left_at C.right_at
    (C.source_gap x hx).1 (C.source_gap x hx).2

theorem sources_below_p (sorted : row.columns.Pairwise (· < ·))
    (shape : row.OrdinaryShape) {p : Nat} (hp : row.p = some p) :
    ∀ x ∈ sources, x < p := by
  have hl := Row.step_lt_length shape
  have atP : row.columns[row.columns.length - (row.step + 1)]? = some p := by
    simpa only [Row.p, fromRight, show 0 < row.step + 1 ∧ row.step + 1 ≤ row.columns.length by omega,
      if_true] using hp
  have rightLe := Row.column_index_le sorted C.right_at atP
    (by have := C.positive; have := C.notLast; omega)
  exact fun x hx => (C.source_gap x hx).2.trans_le rightLe

theorem sources_below_mark (sorted : row.columns.Pairwise (· < ·))
    (shape : row.OrdinaryShape) : ∀ x ∈ sources, x < mark := by
  have hs := Row.step_pos shape
  have rightLe := Row.column_index_le sorted C.right_at C.mark_at
    (by have := C.positive; omega)
  exact fun x hx => (C.source_gap x hx).2.trans_le rightLe

theorem length (sorted : row.columns.Pairwise (· < ·)) (shape : row.OrdinaryShape) :
    (completeMarkRow row mark sources).columns.length = row.columns.length + 2 * sources.length := by
  have h := FullMarkedBLP.completeMarkRow_length (row := NativeBridge.encodeRow row)
    (sorted.imp Nat.ne_of_lt) C.distinct (C.disjoint sorted)
    (fun x hx => (C.sources_below_mark sorted shape x hx).le) C.target_gap
  simpa only [NativeBridge.completeMarkRow_encode, NativeBridge.encode_columns] using h

/-- A long original row has no proper mark, so the exceptional three-column
case cannot be enlarged into an impermissible long shape. -/
theorem shape (sorted : row.columns.Pairwise (· < ·)) (old : row.OrdinaryShape) :
    (completeMarkRow row mark sources).OrdinaryShape := by
  have length := C.length sorted old
  have positive := C.positive
  have before := C.notLast
  rcases old with ⟨len, step⟩ | ⟨len, step⟩ | ⟨len, step⟩
  · omega
  · right; left
    change _ = 2 * (row.step + sources.length) ∧ 1 ≤ row.step + sources.length
    omega
  · right; right
    change _ = 2 * (row.step + sources.length) - 1 ∧ 3 ≤ row.step + sources.length
    omega

theorem encoded_valid (valid : row.BasicValid owner) (shape : row.OrdinaryShape) :
    (NativeBridge.encodeRow (completeMarkRow row mark sources)).CoreValid owner := by
  rw [← NativeBridge.completeMarkRow_encode]
  exact FullMarkedBLP.completeMarkRow_coreValid
    ⟨valid.1, valid.2.1, valid.2.2.1, NativeBridge.shape_encode shape⟩
    C.distinct (C.disjoint valid.1) (fun x hx => (C.sources_below_mark valid.1 shape x hx).le)
    C.target_gap C.before_owner.le

theorem preserves_p (valid : row.BasicValid owner) (shape : row.OrdinaryShape)
    {p : Nat} (hp : row.p = some p) : (completeMarkRow row mark sources).p = some p := by
  have old : (NativeBridge.encodeRow row).CoreValid owner :=
    ⟨valid.1, valid.2.1, valid.2.2.1, NativeBridge.shape_encode shape⟩
  have pLe := FullMarkedBLP.target_position_after_p old (Nat.le_trans (Nat.le_succ _) C.positive)
    C.mark_at hp
  have h := FullMarkedBLP.completeMarkRow_p old hp C.distinct (C.disjoint valid.1)
    C.target_gap pLe (C.sources_below_p valid.1 shape hp)
  simpa only [NativeBridge.completeMarkRow_encode, NativeBridge.encode_p] using h

theorem preserves_e (valid : row.BasicValid owner) (shape : row.OrdinaryShape)
    {e : Nat} (he : row.e = some e) : (completeMarkRow row mark sources).e = some e := by
  obtain ⟨p, hp⟩ := fromRight_exists (xs := row.columns) (by omega : 0 < row.step + 1)
    (by have := Row.step_lt_length shape; omega)
  have old : (NativeBridge.encodeRow row).CoreValid owner :=
    ⟨valid.1, valid.2.1, valid.2.2.1, NativeBridge.shape_encode shape⟩
  have pLess := FullMarkedBLP.row_p_lt_e old hp he
  have h := FullMarkedBLP.completeMarkRow_e old he C.distinct (C.disjoint valid.1) C.target_gap
    (Row.properMark_above_e valid.1 shape C.proper he).le
    (fun x hx => (C.sources_below_p valid.1 shape hp x hx).trans pLess)
  simpa only [NativeBridge.completeMarkRow_encode, NativeBridge.encode_e] using h

theorem preserves_minimum (valid : row.BasicValid owner) (shape : row.OrdinaryShape)
    {minimum : Nat} (hm : row.columns.head? = some minimum) :
    (completeMarkRow row mark sources).columns.head? = some minimum := by
  have old : (NativeBridge.encodeRow row).CoreValid owner :=
    ⟨valid.1, valid.2.1, valid.2.2.1, NativeBridge.shape_encode shape⟩
  have firstLe := FullMarkedBLP.core_head_le_entry old hm C.left_at
  have h := FullMarkedBLP.completeMarkRow_preserves_minimum old hm
    (FullMarkedBLP.core_head_le_entry old hm C.mark_at)
    (fun x hx => (firstLe.trans (C.source_gap x hx).1.le))
  simpa only [NativeBridge.completeMarkRow_encode, NativeBridge.encode_columns] using h

end Row.CompletionGeometry
end IBLP
