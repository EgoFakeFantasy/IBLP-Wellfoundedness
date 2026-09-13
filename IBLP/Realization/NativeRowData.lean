import IBLP.Realization.NativeBlockEdges
import IBLP.Model.WriteOrdinalEdge
import IBLP.Realization.RowGraphData
import FullMarkedBLP.FullRowEdgeSources

namespace IBLP

theorem nativeBlock_row_valid {a : Pattern} (valid : BasicValid a) (shapes : OrdinaryShape a)
    {r j : Nat} {row out : Row} {sources : List Nat} {block : Pattern}
    (hr : rowAt a r = some row) (sourcesRun : nativeSources a r = some sources)
    (proper : ∀ mark ∈ row.marks, row.ProperMark mark)
    (run : nativeBlock row r sources = some block) (entry : block[j]? = some out) :
    out.BasicValid (r + j) := by
  have encodedRow : FullMarkedBLP.rowAt (NativeBridge.encode a) r = some (NativeBridge.encodeRow row) := by simp [hr]
  obtain ⟨computed, computedRun, coreValid⟩ := FullMarkedBLP.nativeBlock_actual_total
    (NativeBridge.valid_encode valid shapes) encodedRow ((NativeBridge.nativeSources_encode a r).trans sourcesRun)
  have same := Option.some.inj (computedRun.symm.trans (NativeBridge.encoded_block run))
  rw [same] at coreValid
  obtain ⟨jb, value⟩ := List.getElem?_eq_some_iff.mp entry
  have eb : j < (NativeBridge.encode block).length := by simpa only [NativeBridge.encode, List.length_map] using jb
  have cv := coreValid j eb
  simp only [NativeBridge.encode, List.getElem_map, value] at cv
  exact NativeBridge.decoded_basic_of_proper cv
    (nativeBlock_proper valid shapes hr sourcesRun proper run out (List.mem_of_getElem? entry))

end IBLP

namespace IBLP.FiniteBoundedData
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (D : FiniteBoundedData stage a)
  (r : FiniteRowIndex a) {row : IBLP.Row} {p e : Nat} {sources : List Nat}
  (hr : IBLP.rowAt a r.val = some row) (hp : row.p = some p) (he : row.e = some e)
  (sourcesRun : IBLP.nativeSources a r.val = some sources)
  (proper : ∀ mark ∈ row.marks, row.ProperMark mark)

include proper in
theorem nativeFamilyGraph_actual_edge {block : IBLP.Pattern} {out : IBLP.Row} {j : Nat}
    (run : IBLP.nativeBlock row r.val sources = some block) (entry : block[j]? = some out)
    {edge : Nat × Nat} (member : edge ∈ out.edgePairs (r.val + j)) :
    ZFSet.pair (D.nativePoint r sources edge.1).toZFSet (D.nativePoint r sources edge.2).toZFSet ∈
      (D.nativeFamilyGraph r hr hp he sourcesRun j).val := by
  have length := IBLP.nativeBlock_length run
  have jb := (List.getElem?_eq_some_iff.mp entry).1
  have bound : j ≤ sources.length := by omega
  have outValid := IBLP.nativeBlock_row_valid D.valid D.shapes hr sourcesRun proper run entry
  have outShape := IBLP.nativeBlock_shapes D.valid D.shapes hr sourcesRun run out (List.mem_of_getElem? entry)
  have endpoint := D.nativeBlock_domain r hr hp he sourcesRun run j bound
  rw [entry, Option.bind_some] at endpoint
  obtain ⟨k, left, right⟩ := IBLP.Row.edgePairs_iff.mp member
  have coreValid : (NativeBridge.encodeRow out).CoreValid (r.val + j) :=
    ⟨outValid.1, outValid.2.1, outValid.2.2.1, NativeBridge.shape_encode outShape⟩
  have sourceBound := (FullMarkedBLP.full_edge_source_bound coreValid endpoint left right).2
  have domainBound := D.nativeDomainIndex_le r hr hp he sourcesRun j
  have eBound := IBLP.Row.column_le_last (D.valid _ _ hr) (IBLP.fromRight_mem he)
  rw [rowEndpoint_eq hr he] at domainBound
  have pointBound : D.nativePoint r sources edge.1 ≤ D.point (nativeDomainIndex r sources j) := by
    rw [D.nativePoint_before r sources (by omega)]
    exact D.point_increasing.monotoneOn
      (by change edge.1 ≤ a.length + 1; have := r.property.2; omega)
      (by change nativeDomainIndex r sources j ≤ a.length + 1; have := r.property.2; omega) sourceBound
  have value := D.nativeBlock_edge_value r hr hp he sourcesRun proper run entry member
  have oldEdge := (D.graph_represents r).write_ordinal_edge
    (pointBound.trans (D.nativeDomain_point_le r hr hp he sourcesRun j)) value
  apply (D.nativeFamilyGraph_edge_iff r hr hp he sourcesRun j _ _).mpr
  exact ⟨(stage.ordinal_mem_hierarchy _ _).mpr (Order.lt_succ_of_le pointBound), oldEdge⟩

include proper in
theorem nativeFamilyGraph_actual_critical {block : IBLP.Pattern} {out : IBLP.Row} {j c : Nat}
    (run : IBLP.nativeBlock row r.val sources = some block) (entry : block[j]? = some out)
    (minimum : out.columns.head? = some c) :
    stage.model.GraphCriticalPoint (D.nativeFamilyGraph r hr hp he sourcesRun j)
      (stage.ordinal (D.nativePoint r sources c)) := by
  have room := (D.valid _ _ hr).2.1
  have first : row.columns.head? = some (row.columns[0]'(by omega)) := by
    simpa only [List.head?_eq_getElem?] using (List.getElem?_eq_getElem (by omega : 0 < row.columns.length))
  have retained := IBLP.nativeBlock_minimum D.valid D.shapes hr sourcesRun proper first run out (List.mem_of_getElem? entry)
  have same : c = row.columns[0] := Option.some.inj (minimum.symm.trans retained)
  have oldMinimum : row.columns.head? = some c := by rw [same]; exact first
  have cb := IBLP.Row.column_le_last (D.valid _ _ hr) (List.mem_of_head? oldMinimum)
  rw [D.nativePoint_before r sources cb]
  exact D.nativeFamilyGraph_critical r hr hp he sourcesRun oldMinimum j

/-- A complete actual graph for any generated family row: source and
target elementary ranks, the literal minimum as critical point, and all
literal step pairs, including the implicit target. -/
noncomputable def nativeFamilyRowData {block : IBLP.Pattern} {out : IBLP.Row} {j : Nat}
    (run : IBLP.nativeBlock row r.val sources = some block) (entry : block[j]? = some out) :
    RowGraphData stage (D.nativePoint r sources) (r.val + j) out where
  graph := D.nativeFamilyGraph r hr hp he sourcesRun j
  elementary := by
    intro endpoint atEndpoint
    have length := IBLP.nativeBlock_length run
    have jb := (List.getElem?_eq_some_iff.mp entry).1
    exact D.nativeFamilyGraph_actual_elementary r hr hp he sourcesRun run j (by omega) entry atEndpoint
  critical := fun _ minimum => D.nativeFamilyGraph_actual_critical r hr hp he sourcesRun proper run entry minimum
  edges := fun _ member => D.nativeFamilyGraph_actual_edge r hr hp he sourcesRun proper run entry member

end IBLP.FiniteBoundedData
