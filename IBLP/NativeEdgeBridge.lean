import IBLP.NativeMinimum
import IBLP.Realization.NativeActualDomains

namespace IBLP

theorem Row.edgePairs_iff {row : Row} {owner x y : Nat} :
    (x, y) ∈ row.edgePairs owner ↔ ∃ i,
      (row.columns ++ [owner + 1])[i]? = some x ∧
      (row.columns ++ [owner + 1])[i + row.step]? = some y := by
  constructor
  · intro member
    obtain ⟨i, bound, value⟩ := List.mem_iff_getElem.mp member
    have bounds : i < (row.columns ++ [owner + 1]).length ∧
        row.step + i < (row.columns ++ [owner + 1]).length := by
      simpa only [Row.edgePairs, List.length_zip, lt_min_iff, List.length_drop,
        Nat.lt_sub_iff_add_lt, Nat.add_comm] using bound
    have values : ((row.columns ++ [owner + 1])[i], (row.columns ++ [owner + 1])[row.step + i]) = (x, y) := by
      simpa only [Row.edgePairs, List.getElem_zip, List.getElem_drop] using value
    refine ⟨i, List.getElem?_eq_some_iff.mpr ⟨bounds.1, congrArg Prod.fst values⟩, ?_⟩
    exact List.getElem?_eq_some_iff.mpr ⟨by omega, by simpa only [Nat.add_comm] using congrArg Prod.snd values⟩
  · rintro ⟨i, left, right⟩
    obtain ⟨lb, lv⟩ := List.getElem?_eq_some_iff.mp left
    obtain ⟨rb, rv⟩ := List.getElem?_eq_some_iff.mp right
    apply List.mem_iff_getElem.mpr
    refine ⟨i, ?_, ?_⟩
    · simp only [Row.edgePairs, List.length_zip, List.length_drop, lt_min_iff]
      omega
    · simp only [Row.edgePairs, List.getElem_zip, List.getElem_drop, Nat.add_comm row.step i, lv, rv]

end IBLP

namespace IBLP.FiniteBoundedData
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (D : FiniteBoundedData stage a)

theorem nativePoint_before (r : FiniteRowIndex a) (sources : List Nat) {i : Nat} (bound : i ≤ r.val) :
    D.nativePoint r sources i = D.point i :=
  FullMarkedBLP.nativeColumnValues_before D.point (D.nativeFresh r sources) bound

theorem nativeFresh_source_rank (r : FiniteRowIndex a) {sources : List Nat} {x : Nat}
    (run : IBLP.nativeSources a r.val = some sources) (member : x ∈ sources) :
    D.nativeFresh r sources (sources.filter (· < x)).length = D.nativeImage r x := by
  have sorted : sources.reverse.Pairwise (· < ·) := (IBLP.nativeSources_decreasing D.valid run).reverse
  have entry := FullMarkedBLP.sorted_get_at_rank sorted (List.mem_reverse.mpr member)
  simp only [List.filter_reverse, List.length_reverse] at entry
  unfold nativeFresh
  rw [entry, Option.getD_some]

theorem nativeImage_edges (r : FiniteRowIndex a) {row : IBLP.Row} (hr : IBLP.rowAt a r.val = some row) :
    (NativeBridge.encodeRow row).RealizesEdges (stage.rho (D.map r)) D.point r.val := by
  intro i x y left right
  exact (D.graph_represents r).read_ordinal_edge
    (D.edges r row hr (x, y) (IBLP.Row.edgePairs_iff.mpr ⟨i, left, right⟩))

end IBLP.FiniteBoundedData
