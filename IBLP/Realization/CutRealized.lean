import IBLP.Realization.PrefixRealized
import IBLP.Realization.CopyPoints
import IBLP.CutGeometry

namespace IBLP
open FullMarkedBLP
universe u

namespace MarkedRealization
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (R : MarkedRealization stage a)

theorem cut_realization_exists {b : IBLP.Pattern} (run : IBLP.cut a = some b) :
    ∃ S : MarkedRealization stage b, S.top = R.data.point a.length ∧ S.top < R.top := by
  obtain ⟨positive, same⟩ := IBLP.cut_decomposition run
  subst b
  refine ⟨R.take (a.length - 1), ?_, ?_⟩
  · rw [R.take_top, List.length_take, Nat.min_eq_left (Nat.sub_le _ _), Nat.sub_add_cancel positive]
  · rw [R.take_top, List.length_take, Nat.min_eq_left (Nat.sub_le _ _), Nat.sub_add_cancel positive]
    change R.data.point a.length < R.data.top
    rw [← R.data.point_top]
    exact R.data.point_increasing (by change a.length ≤ a.length + 1; omega)
      (by change a.length + 1 ≤ a.length + 1; rfl) (by omega)

end MarkedRealization

namespace BoundedRealization
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (R : BoundedRealization stage a)

/-- The parameter-zero, successor and failed-first-copy cases retain a
complete realization in the same model and strictly lower its top. -/
theorem cut_realization_exists {b : IBLP.Pattern} (run : IBLP.cut a = some b) :
    ∃ S : BoundedRealization stage b, S.top = R.data.point a.length ∧ S.top < R.top := by
  obtain ⟨positive, same⟩ := IBLP.cut_decomposition run
  subst b
  refine ⟨R.take (a.length - 1), ?_, ?_⟩
  · rw [R.take_top, List.length_take, Nat.min_eq_left (Nat.sub_le _ _), Nat.sub_add_cancel positive]
  · rw [R.take_top, List.length_take, Nat.min_eq_left (Nat.sub_le _ _), Nat.sub_add_cancel positive]
    change R.data.point a.length < R.data.top
    rw [← R.data.point_top]
    exact R.data.point_increasing (by change a.length ≤ a.length + 1; omega)
      (by change a.length + 1 ≤ a.length + 1; rfl) (by omega)

end BoundedRealization
end IBLP
