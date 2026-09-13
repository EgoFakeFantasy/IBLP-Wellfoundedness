import IBLP.Realization.NativeTopEdges

namespace IBLP.FiniteBoundedData
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (D : FiniteBoundedData stage a)

/-- All actual family step edges are values of the original bounded map.
The restriction to each row's actual source domain is performed afterward. -/
theorem nativeBlock_edges (r : FiniteRowIndex a) {row : IBLP.Row} {p e : Nat} {sources : List Nat} {block : IBLP.Pattern}
    (hr : IBLP.rowAt a r.val = some row) (hp : row.p = some p) (he : row.e = some e)
    (sourcesRun : IBLP.nativeSources a r.val = some sources)
    (proper : ∀ mark ∈ row.marks, row.ProperMark mark)
    (run : IBLP.nativeBlock row r.val sources = some block) :
    FullMarkedBLP.BlockEdges (stage.rho (D.map r)) (D.nativePoint r sources) r.val (NativeBridge.encode block) := by
  have valid := NativeBridge.valid_encode D.valid D.shapes
  have encodedRow : FullMarkedBLP.rowAt (NativeBridge.encode a) r.val = some (NativeBridge.encodeRow row) := by simp [hr]
  have encodedSources := (NativeBridge.nativeSources_encode a r.val).trans sourcesRun
  have encodedBlock := NativeBridge.encoded_block run
  have hv := valid _ _ encodedRow
  cases sources with
  | nil =>
    have same : block = [row] := (Option.some.inj run).symm
    subst block
    intro j jb
    have zero : j = 0 := by
      simp only [NativeBridge.encode, List.length_map, List.length_singleton] at jb
      omega
    subst j
    have points : D.nativePoint r [] = D.point := by
      funext i
      have value := D.nativePoint_old r [] i
      simpa only [IBLP.shiftAfter, List.length_nil, Nat.add_zero, ite_self] using value
    simpa only [NativeBridge.encode, List.map_cons, List.map_nil, List.getElem_cons_zero, Nat.add_zero, points]
      using D.nativeImage_edges r hr
  | cons s ss =>
    have nonempty : s :: ss ≠ [] := by simp
    have eligible := FullMarkedBLP.nativeSources_nonempty_eligible encodedRow encodedSources nonempty
    have minStep := FullMarkedBLP.nativeSources_nonempty_step_ge_two hv encodedRow encodedSources nonempty
    change 2 ≤ row.step at minStep
    have topValid := FullMarkedBLP.nativeTop_actual_coreValid valid encodedRow encodedSources
    have topLength := FullMarkedBLP.nativeTop_actual_length valid encodedRow encodedSources
    have targets := FullMarkedBLP.nativeTop_contains_targets hv (s :: ss)
    have topProper := NativeBridge.top_weak_proper D.valid D.shapes hr sourcesRun proper
    have topEdges := D.nativeTop_edges r hr hp he sourcesRun nonempty
    rw [← NativeBridge.nativeTop_encode] at topEdges
    by_cases medium : row.columns.length = 2 * row.step
    · obtain ⟨result, computed, resultEdges⟩ := FullMarkedBLP.nativeBlockDown_medium_edges ss.length
        (stage.rho (D.map r)) (D.nativePoint r (s :: ss)) topValid topProper topEdges
        (by change _ = 2 * (row.step + (s :: ss).length); change _ = row.columns.length + 2 * (s :: ss).length at topLength; omega)
        (by change _ ≤ row.step + (s :: ss).length; simp; omega) targets
      have actual : FullMarkedBLP.nativeBlockDown (s :: ss).length (r.val + (s :: ss).length) true
          (FullMarkedBLP.nativeTop (NativeBridge.encodeRow row) r.val (s :: ss)) = some (NativeBridge.encode block) := by
        simpa only [FullMarkedBLP.nativeBlock, List.isEmpty_cons, Bool.false_eq_true, if_false,
          NativeBridge.encode_columns, NativeBridge.encode_step, medium, beq_self_eq_true] using encodedBlock
      have same := Option.some.inj (computed.symm.trans actual)
      rwa [same] at resultEdges
    · have short := FullMarkedBLP.Row.short_shape_of_eligible_ne_medium hv.2.2.2 eligible medium
      change row.columns.length + 1 = 2 * row.step ∧ 3 ≤ row.step at short
      obtain ⟨result, computed, resultEdges⟩ := FullMarkedBLP.nativeBlockDown_short_edges (s :: ss).length
        (stage.rho (D.map r)) (D.nativePoint r (s :: ss)) topValid topProper topEdges
        (by change _ + 1 = 2 * (row.step + (s :: ss).length); change _ = row.columns.length + 2 * (s :: ss).length at topLength; omega)
        (by change _ ≤ row.step + (s :: ss).length; omega) targets
      have notMedium : (row.columns.length == 2 * row.step) = false := by simp [medium]
      have actual : FullMarkedBLP.nativeBlockDown (s :: ss).length (r.val + (s :: ss).length) false
          (FullMarkedBLP.nativeTop (NativeBridge.encodeRow row) r.val (s :: ss)) = some (NativeBridge.encode block) := by
        simpa only [FullMarkedBLP.nativeBlock, List.isEmpty_cons, Bool.false_eq_true, if_false,
          NativeBridge.encode_columns, NativeBridge.encode_step, notMedium] using encodedBlock
      have same := Option.some.inj (computed.symm.trans actual)
      rwa [same] at resultEdges

theorem nativeBlock_edge_value (r : FiniteRowIndex a) {row out : IBLP.Row} {p e j : Nat} {sources : List Nat} {block : IBLP.Pattern}
    (hr : IBLP.rowAt a r.val = some row) (hp : row.p = some p) (he : row.e = some e)
    (sourcesRun : IBLP.nativeSources a r.val = some sources)
    (proper : ∀ mark ∈ row.marks, row.ProperMark mark)
    (run : IBLP.nativeBlock row r.val sources = some block) (entry : block[j]? = some out)
    {edge : Nat × Nat} (member : edge ∈ out.edgePairs (r.val + j)) :
    stage.rho (D.map r) (D.nativePoint r sources edge.1) = D.nativePoint r sources edge.2 := by
  obtain ⟨jb, value⟩ := List.getElem?_eq_some_iff.mp entry
  have eb : j < (NativeBridge.encode block).length := by simpa only [NativeBridge.encode, List.length_map] using jb
  have edges := D.nativeBlock_edges r hr hp he sourcesRun proper run j eb
  simp only [NativeBridge.encode, List.getElem_map, value] at edges
  obtain ⟨k, left, right⟩ := IBLP.Row.edgePairs_iff.mp member
  exact edges k edge.1 edge.2 left right

end IBLP.FiniteBoundedData
