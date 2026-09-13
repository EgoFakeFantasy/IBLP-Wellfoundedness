import IBLP.Realization.CopyFrozenClosure

namespace IBLP.BoundedRealization
universe u

/-- Every actual old cursor still present after the cut belongs to one
of the finitely many copied blocks, including the original last-row base
of the first block. No positive copy-count hypothesis is needed. -/
theorem copies_cut_cursor_block {stage : ModelStage.{u}} {a copied initial : Pattern}
    (R : BoundedRealization stage a) {last : Row} {p m i : Nat}
    (hlast : a.getLast? = some last) (hp : last.p = some p)
    (copies : rawCopies m a = some copied) (cut : IBLP.cut copied = some initial)
    (lower : a.length ≤ i) (upper : i ≤ initial.length) :
    ∃ k, k < m ∧ a.length + k * (a.length - p) ≤ i ∧
      i < a.length + (k + 1) * (a.length - p) := by
  have pred : predecessor a a.length = some p := by simp [predecessor, getLast_rowAt hlast, hp]
  have smaller := predecessor_lt R.data.valid R.data.shapes pred
  have widthPositive : 0 < a.length - p := by omega
  have copiedLength := (R.data.rawCopies_length_control R.proper hlast hp copies).1
  have cutLength := cut_length cut
  have endBound : i < a.length + m * (a.length - p) := by omega
  let k := (i - a.length) / (a.length - p)
  have division := Nat.mod_add_div (i - a.length) (a.length - p)
  have remainder := Nat.mod_lt (i - a.length) widthPositive
  have first : k * (a.length - p) ≤ i - a.length := by
    dsimp [k]
    rw [Nat.mul_comm]
    omega
  have last : i - a.length < (k + 1) * (a.length - p) := by
    dsimp [k]
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm ((i - a.length) / (a.length - p))]
    omega
  refine ⟨k, ?_, by omega, by omega⟩
  by_contra reverse
  have product := Nat.mul_le_mul_right (a.length - p) (Nat.le_of_not_gt reverse)
  omega

end IBLP.BoundedRealization
