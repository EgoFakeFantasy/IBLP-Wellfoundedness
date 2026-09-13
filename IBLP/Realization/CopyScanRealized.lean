import IBLP.Realization.CopyScanClosure
import IBLP.ScanTotal

namespace IBLP.BoundedRealization
universe u

theorem copies_cut_saturated_prefix {stage savedStage : ModelStage.{u}} {a copied initial : Pattern}
    (R : BoundedRealization stage a) (entry : MarkedRealization savedStage initial)
    {last : Row} {p m : Nat} (hlast : a.getLast? = some last) (hp : last.p = some p)
    (copies : rawCopies m a = some copied) (cut : IBLP.cut copied = some initial) :
    SaturatedBefore initial a.length := by
  have length := (R.data.rawCopies_length_control R.proper hlast hp copies).1
  apply saturatedBefore_of_prefix entry.data.valid entry.data.shapes _ (R.saturated.before a.length)
  intro i before
  rw [(cut_decomposition cut).2, rowAt_take (by omega : i ≤ copied.length - 1)]
  exact rawCopies_prefix copies before

/-- A successful original copied/cut scan has a complete saturated
realization in the entrance model and preserves its top. All intermediate
geometry and semantic history obligations are discharged. -/
theorem copies_scan_realized {stage savedStage : ModelStage.{u}} {a copied initial result : Pattern}
    (R : BoundedRealization stage a) (entry : MarkedRealization savedStage initial)
    {last : Row} {p m : Nat} (hlast : a.getLast? = some last) (hp : last.p = some p)
    (copies : rawCopies m a = some copied) (cut : IBLP.cut copied = some initial)
    (run : scan initial a.length = some result) :
    ∃ S : BoundedRealization savedStage result, S.top = entry.top := by
  have history := R.copies_scan_syntax_history entry hlast hp copies cut
  have saturated := scan_saturated_of_history history (R.copies_cut_saturated_prefix entry hlast hp copies cut) run
  obtain ⟨rec, cursor, reached, _⟩ := scan_reaches_end run
  obtain ⟨old, names, labeled, _⟩ := reached.labeled
  obtain ⟨S, top, _⟩ := R.copies_scan_realizations entry hlast hp copies cut result rec old names labeled
  exact ⟨S.withSaturation saturated, top⟩

/-- The complete original scan always returns, for every finite copied
input, including zero copies and an already exhausted post-cut scan. -/
theorem copies_scan_total_realized {stage savedStage : ModelStage.{u}} {a copied initial : Pattern}
    (R : BoundedRealization stage a) (entry : MarkedRealization savedStage initial)
    {last : Row} {p m : Nat} (hlast : a.getLast? = some last) (hp : last.p = some p)
    (copies : rawCopies m a = some copied) (cut : IBLP.cut copied = some initial) :
    ∃ result, scan initial a.length = some result ∧
      ∃ S : BoundedRealization savedStage result, S.top = entry.top := by
  obtain ⟨result, run⟩ := scan_total_of_history (rowAt_pos (getLast_rowAt hlast))
    (R.copies_scan_syntax_history entry hlast hp copies cut)
  exact ⟨result, run, R.copies_scan_realized entry hlast hp copies cut run⟩

end IBLP.BoundedRealization
