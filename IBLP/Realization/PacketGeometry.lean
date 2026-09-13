import IBLP.Realization.CompletionMarks

namespace IBLP.FiniteBoundedData
universe u
variable {stage : ModelStage.{u}} {a : Pattern} (D : FiniteBoundedData stage a)

/-- Order reflection for actual finite point indices uses the monotone
clipped ordinal action, and does not presuppose that an input lies in the
carrier domain. This avoids assuming the source gap being proved. -/
theorem nativeImage_lt_reflect (r : FiniteRowIndex a) {i j : Nat}
    (hi : i ≤ a.length + 1) (hj : j ≤ a.length + 1)
    (less : D.nativeImage r i < D.nativeImage r j) : i < j := by
  by_contra reverse
  have points := D.point_increasing.monotoneOn hj hi (Nat.le_of_not_gt reverse)
  exact not_lt_of_ge (stage.rho_monotone (D.map r) points) less

/-- The full packet equations and the already established target gap
force the source packet into the adjacent paired-source gap. In
particular, no source-domain or source-gap premise is used. -/
theorem completionGeometry_of_packet (r : FiniteRowIndex a) {row : Row} {mark : Nat}
    {sources : List Nat} (hr : rowAt a r.val = some row) (proper : row.ProperMark mark)
    (distinct : sources.Nodup) (inside : ∀ s ∈ sources, s ≤ a.length + 1)
    (targetGap : ∀ x, mark < x → x ≤ mark + sources.length → x ∉ row.columns)
    (before : mark + sources.length < r.val)
    (packet : ∀ s ∈ sources, D.nativeImage r s = D.point (mark + 1 + (sources.filter (· < s)).length)) :
    Nonempty (row.CompletionGeometry r.val mark sources) := by
  obtain ⟨index, atMark, positive, notLast⟩ := proper
  have valid := D.valid _ _ hr
  have shape := D.shapes row (rowAt_mem hr)
  have stepPositive := Row.step_pos shape
  let left := row.columns[index - row.step]'(by omega)
  let right := row.columns[index - row.step + 1]'(by omega)
  let next := row.columns[index + 1]'notLast
  have atLeft : row.columns[index - row.step]? = some left := List.getElem?_eq_getElem (by omega)
  have atRight : row.columns[index - row.step + 1]? = some right := List.getElem?_eq_getElem (by omega)
  have atNext : row.columns[index + 1]? = some next := List.getElem?_eq_getElem notLast
  have markNext : mark < next := by
    obtain ⟨hm, vm⟩ := List.getElem?_eq_some_iff.mp atMark
    obtain ⟨hn, vn⟩ := List.getElem?_eq_some_iff.mp atNext
    simpa only [vm, vn] using List.pairwise_iff_getElem.mp valid.1 index (index + 1) hm hn (by omega)
  have packetNext : mark + sources.length < next := by
    by_contra reverse
    exact targetGap next markNext (by omega) (List.mem_of_getElem? atNext)
  have leftEdge : D.nativeImage r left = D.point mark := by
    apply D.nativeImage_edges r hr (index - row.step) left mark (FullMarkedBLP.full_entry_of_core atLeft)
    simp only [NativeBridge.encode_step]
    rw [Nat.sub_add_cancel (by omega : row.step ≤ index)]
    exact FullMarkedBLP.full_entry_of_core atMark
  have rightEdge : D.nativeImage r right = D.point next := by
    apply D.nativeImage_edges r hr (index - row.step + 1) right next (FullMarkedBLP.full_entry_of_core atRight)
    simp only [NativeBridge.encode_step]
    have position : index - row.step + 1 + row.step = index + 1 := by omega
    rw [position]
    exact FullMarkedBLP.full_entry_of_core atNext
  have leftBound := Row.column_le_last valid (List.mem_of_getElem? atLeft)
  have rightBound := Row.column_le_last valid (List.mem_of_getElem? atRight)
  have nextBound := Row.column_le_last valid (List.mem_of_getElem? atNext)
  have ownerBound := r.property.2
  refine ⟨⟨index, left, right, positive, notLast, atMark, atLeft, atRight,
    distinct, ?_, targetGap, before⟩⟩
  intro s member
  have rankBound : (sources.filter (· < s)).length < sources.length :=
    List.length_filter_lt_length_iff_exists.mpr ⟨s, member, by simp⟩
  have lower : D.nativeImage r left < D.nativeImage r s := by
    rw [leftEdge, packet s member]
    exact D.point_increasing (by change mark ≤ a.length + 1; omega)
      (by change mark + 1 + (sources.filter (· < s)).length ≤ a.length + 1; omega) (by omega)
  have upper : D.nativeImage r s < D.nativeImage r right := by
    rw [rightEdge, packet s member]
    exact D.point_increasing
      (by change mark + 1 + (sources.filter (· < s)).length ≤ a.length + 1; omega)
      (by change next ≤ a.length + 1; omega) (by omega)
  exact ⟨D.nativeImage_lt_reflect r (by omega) (inside s member) lower,
    D.nativeImage_lt_reflect r (inside s member) (by omega) upper⟩

end IBLP.FiniteBoundedData
