import IBLP.Realization.NativeRowData
import IBLP.Realization.ShiftRowData
import IBLP.NativeRows

namespace IBLP.FiniteBoundedData
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (D : FiniteBoundedData stage a)
  (r : FiniteRowIndex a) {row : IBLP.Row} {p e : Nat} {sources : List Nat}
  (hr : IBLP.rowAt a r.val = some row) (hp : row.p = some p) (he : row.e = some e)
  (sourcesRun : IBLP.nativeSources a r.val = some sources) (proper : IBLP.ProperMarks a)

/-- The actual row graphs of the full native output: saved prefix graphs,
actual restrictions for the family, and saved relabeled suffix graphs. -/
noncomputable def nativeRowGraphData {b : IBLP.Pattern} (run : IBLP.native a r.val = some (b, sources))
    (i : FiniteRowIndex b) (out : IBLP.Row) (atOut : IBLP.rowAt b i.val = some out) :
    RowGraphData stage (D.nativePoint r sources) i.val out := by
  by_cases before : i.val < r.val
  · have atOld : IBLP.rowAt a i.val = some out := (IBLP.native_prefix_rowAt run before).symm.trans atOut
    let oldIndex : FiniteRowIndex a := ⟨i.val, i.property.1, (IBLP.rowAt_bounds atOld).2⟩
    exact (D.savedRowData oldIndex atOld).repoint (D.valid _ _ atOld) (D.shapes out (rowAt_mem atOld))
      (fun k bound => (D.nativePoint_before r sources (by change k ≤ i.val + 1 at bound; omega)).symm)
  by_cases family : i.val ≤ r.val + sources.length
  · have blocks : ∃ block, IBLP.nativeBlock row r.val sources = some block := by
      obtain ⟨oldRow, block, atRow, _, blockRun, _⟩ := IBLP.native_decomposition run
      have same := Option.some.inj (atRow.symm.trans hr)
      subst oldRow
      exact ⟨block, blockRun⟩
    let block := blocks.choose
    have blockRun : IBLP.nativeBlock row r.val sources = some block := blocks.choose_spec
    have length := IBLP.nativeBlock_length blockRun
    have owner : r.val + (i.val - r.val) = i.val := by omega
    have atBlock : block[i.val - r.val]? = some out := by
      rw [← IBLP.native_family_rowAt hr run blockRun (by omega), owner]
      exact atOut
    let data := D.nativeFamilyRowData r hr hp he sourcesRun (proper row (rowAt_mem hr)) blockRun atBlock
    exact {
      graph := data.graph
      elementary := fun endpoint atEndpoint => by simpa only [owner] using data.elementary endpoint atEndpoint
      critical := data.critical
      edges := fun edge member => by
        have member' : edge ∈ out.edgePairs (r.val + (i.val - r.val)) := by rwa [owner]
        exact data.edges edge member' }
  · have after : r.val < i.val - sources.length := by omega
    have owner : i.val - sources.length + sources.length = i.val := by omega
    have suffix := IBLP.native_suffix_rowAt run after
    rw [owner, atOut] at suffix
    have oldRows := Option.map_eq_some_iff.mp suffix.symm
    let oldRow := oldRows.choose
    have atOld : IBLP.rowAt a (i.val - sources.length) = some oldRow := oldRows.choose_spec.1
    have same : oldRow.shiftAfter r.val sources.length = out := oldRows.choose_spec.2
    let oldIndex : FiniteRowIndex a :=
      ⟨i.val - sources.length, (IBLP.rowAt_bounds atOld).1, (IBLP.rowAt_bounds atOld).2⟩
    let data := (D.savedRowData oldIndex atOld).shiftAfter r.val sources.length after
      (D.nativePoint_old r sources)
    refine { graph := data.graph, elementary := ?_, critical := ?_, edges := ?_ }
    · intro endpoint atEndpoint
      rw [← same] at atEndpoint
      have value := data.elementary endpoint atEndpoint
      change stage.InternalGraphElementary _ (D.nativePoint r sources (i.val - sources.length + sources.length + 1)) _ at value
      simpa only [owner] using value
    · intro c minimum
      rw [← same] at minimum
      exact data.critical c minimum
    · intro edge member
      have member' : edge ∈ (oldRow.shiftAfter r.val sources.length).edgePairs (i.val - sources.length + sources.length) := by
        simpa only [owner, same] using member
      exact data.edges edge member'

noncomputable def nativeTheta (r : FiniteRowIndex a) (sources : List Nat) (b : IBLP.Pattern) :
    Fin (b.length + 2) → Ordinal.{u} := fun i => D.nativePoint r sources i.val

theorem nativeTheta_at (r : FiniteRowIndex a) (sources : List Nat) (b : IBLP.Pattern)
    (i : Nat) (bound : i ≤ b.length + 1) :
    finiteThetaExtension (D.nativeTheta r sources b) i = D.nativePoint r sources i := by
  simp only [finiteThetaExtension, Nat.min_eq_left bound, nativeTheta]

/-- Complete finite point and row-graph data for the original native
program. New accurate mark certificates are a separate remaining obligation. -/
noncomputable def nativeData {b : IBLP.Pattern} (run : IBLP.native a r.val = some (b, sources)) :
    FiniteBoundedData stage b := by
  have geometry := IBLP.native_preserves_syntax D.valid D.shapes proper run
  have length := IBLP.native_length run
  let chosen (i : FiniteRowIndex b) : IBLP.Row := (rowAt_exists i.property.1 i.property.2).choose
  have atChosen (i : FiniteRowIndex b) : IBLP.rowAt b i.val = some (chosen i) :=
    (rowAt_exists i.property.1 i.property.2).choose_spec
  let rows (i : FiniteRowIndex b) :
      RowGraphData stage (finiteThetaExtension (D.nativeTheta r sources b)) i.val (chosen i) :=
    (D.nativeRowGraphData r hr hp he sourcesRun proper run i (chosen i) (atChosen i)).repoint
      (geometry.1 _ _ (atChosen i)) (geometry.2.1 _ (rowAt_mem (atChosen i)))
      (fun k bound => (D.nativeTheta_at r sources b k (by have := i.property.2; omega)).symm)
  refine {
    theta := D.nativeTheta r sources b
    increasing := ?_
    inaccessible := fun i => D.nativePoint_inaccessible r sources i.val
    valid := geometry.1
    shapes := geometry.2.1
    graph := fun i => (rows i).graph
    elementary := ?_
    critical := ?_
    edges := ?_ }
  · intro i k less
    exact D.nativePoint_increasing r hr hp he sourcesRun
      (by change i.val ≤ a.length + sources.length + 1; have := i.isLt; omega)
      (by change k.val ≤ a.length + sources.length + 1; have := k.isLt; omega) less
  · intro i
    obtain ⟨out, atOut, endpoint⟩ := finiteRow_endpoint_exists geometry.2.1 i
    have same : out = chosen i := Option.some.inj (atOut.symm.trans (atChosen i))
    subst out
    exact (rows i).elementary (rowEndpoint b i.val) endpoint
  · intro i out c atOut minimum
    have same : out = chosen i := Option.some.inj (atOut.symm.trans (atChosen i))
    subst out
    exact (rows i).critical c minimum
  · intro i out atOut edge member
    have same : out = chosen i := Option.some.inj (atOut.symm.trans (atChosen i))
    subst out
    exact (rows i).edges edge member

theorem nativeData_point {b : IBLP.Pattern} (run : IBLP.native a r.val = some (b, sources))
    (i : Nat) (bound : i ≤ b.length + 1) :
    (D.nativeData r hr hp he sourcesRun proper run).point i = D.nativePoint r sources i :=
  D.nativeTheta_at r sources b i bound

theorem nativeData_top {b : IBLP.Pattern} (run : IBLP.native a r.val = some (b, sources)) :
    (D.nativeData r hr hp he sourcesRun proper run).top = D.top := by
  rw [← point_top, D.nativeData_point r hr hp he sourcesRun proper run (b.length + 1) le_rfl,
    IBLP.native_length run, D.nativePoint_top]

end IBLP.FiniteBoundedData
