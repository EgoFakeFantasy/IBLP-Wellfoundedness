import IBLP.Saturation
import IBLP.ScanPrefix

namespace IBLP

theorem saturatedBefore_of_prefix {a b : Pattern} {bound : Nat} (valid : BasicValid b)
    (shapes : OrdinaryShape b) (same : ∀ i, i < bound → rowAt b i = rowAt a i)
    (saturated : SaturatedBefore a bound) : SaturatedBefore b bound := by
  intro i row p e q before hr hp he hq
  have atOld := (same i before).symm.trans hr
  have endpoint := fromRight_le_last (valid _ _ hr).1 (valid _ _ hr).2.2.1
    (Row.step_pos (shapes row (rowAt_mem hr))) he
  have oldQ : penultimate a e = some q := by
    simpa only [penultimate, same e (by omega : e < bound)] using hq
  exact saturated i row p e q before atOld hp he oldQ

theorem completeFrozenMarks_preserves_saturation_prefix {a : Pattern} {rec : Records} {r : Nat}
    (valid : BasicValid (completeFrozenMarks a rec r)) (shapes : OrdinaryShape (completeFrozenMarks a rec r))
    (saturated : SaturatedBefore a r) : SaturatedBefore (completeFrozenMarks a rec r) r :=
  saturatedBefore_of_prefix valid shapes (fun i before => completeFrozenMarks_other_row (by omega)) saturated

/-- The precise remaining syntactic history obligation for a fixed scan.
Its proof is supplied by completion's event induction, not by this definition. -/
def ScanSyntaxHistory (initial : Pattern) (start : Nat) : Prop :=
  ∀ current rec cursor, ScanReach initial start current rec cursor →
    BasicValid (completeFrozenMarks current rec cursor) ∧
      OrdinaryShape (completeFrozenMarks current rec cursor) ∧
      ProperMarks (completeFrozenMarks current rec cursor)

theorem ScanReach.saturation_prefix {initial current : Pattern} {start cursor : Nat} {rec : Records}
    (history : ScanSyntaxHistory initial start) (initialSat : SaturatedBefore initial start)
    (reach : ScanReach initial start current rec cursor) : SaturatedBefore current cursor := by
  induction reach with
  | start => exact initialSat
  | @next before after record owner sources previous bound run ih =>
    have invariants := history before record owner previous
    exact native_advances_saturation invariants.1 invariants.2.1 invariants.2.2
      (completeFrozenMarks_preserves_saturation_prefix invariants.1 invariants.2.1 ih) run

/-- Once actual intermediate syntax is established, a successful original
scan is saturated. No saturation premise is imposed on unprocessed rows. -/
theorem scan_saturated_of_history {initial result : Pattern} {start : Nat}
    (history : ScanSyntaxHistory initial start) (initialSat : SaturatedBefore initial start)
    (run : scan initial start = some result) : Saturated result := by
  obtain ⟨rec, cursor, reach, ended⟩ := scan_reaches_end run
  exact (reach.saturation_prefix history initialSat).all ended

end IBLP
