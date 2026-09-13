import IBLP.Realization.RowGraphData
import IBLP.MappedColumns

namespace IBLP
open FullMarkedBLP
universe u

theorem mapped_total {α β : Type} (f : α → β) (xs : List α) : MapsEntries (some ∘ f) xs (xs.map f) := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact .cons rfl ih

/-- Relabel a suffix row while preserving its actual saved graph. -/
noncomputable def RowGraphData.shiftAfter {stage : ModelStage.{u}} {point point' : Nat → Ordinal.{u}}
    {owner : Nat} {row : IBLP.Row} (G : RowGraphData stage point owner row)
    (r h : Nat) (after : r < owner) (same : ∀ i, point' (IBLP.shiftAfter r h i) = point i) :
    RowGraphData stage point' (owner + h) (row.shiftAfter r h) := by
  have mapped := mapped_total (IBLP.shiftAfter r h) row.columns
  have endpoint : IBLP.shiftAfter r h (owner + 1) = owner + h + 1 := by
    simp only [IBLP.shiftAfter, if_pos (by omega : r < owner + 1)]
    omega
  have points : point' (owner + h + 1) = point (owner + 1) := by rw [← endpoint]; exact same _
  have full : MapsEntries (some ∘ IBLP.shiftAfter r h) (row.columns ++ [owner + 1])
      ((row.shiftAfter r h).columns ++ [owner + h + 1]) :=
    mapped_append mapped (.cons (by simp only [Function.comp_apply, endpoint]) .nil)
  refine { graph := G.graph, elementary := ?_, critical := ?_, edges := ?_ }
  · intro e he
    obtain ⟨old, atOld, image⟩ := mapped_fromRight mapped he
    have eq : IBLP.shiftAfter r h old = e := Option.some.inj image
    rw [← eq, same, points]
    exact G.elementary old atOld
  · intro c hc
    have index : (row.shiftAfter r h).columns[0]? = some c := by simpa only [List.head?_eq_getElem?] using hc
    obtain ⟨old, atOld, image⟩ := mapped.at index
    have eq : IBLP.shiftAfter r h old = c := Option.some.inj image
    rw [← eq, same]
    exact G.critical old (by simpa only [List.head?_eq_getElem?] using atOld)
  · intro edge member
    obtain ⟨old, oldEdge, left, right⟩ := mapped_zip_drop full row.step member
    have le : IBLP.shiftAfter r h old.1 = edge.1 := Option.some.inj left
    have re : IBLP.shiftAfter r h old.2 = edge.2 := Option.some.inj right
    rw [← le, ← re, same, same]
    exact G.edges old oldEdge

namespace FiniteBoundedData
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (D : FiniteBoundedData stage a)

noncomputable def savedRowData (r : FiniteRowIndex a) {row : IBLP.Row} (hr : IBLP.rowAt a r.val = some row) :
    RowGraphData stage D.point r.val row where
  graph := D.graph r
  elementary := by
    intro e he
    simpa only [point, rowEndpoint_eq hr he] using D.elementary r
  critical := fun _ hc => D.critical r row _ hr hc
  edges := D.edges r row hr

end FiniteBoundedData
end IBLP
