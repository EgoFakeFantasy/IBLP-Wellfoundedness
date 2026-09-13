import IBLP.Realization.NextCopy
import IBLP.RawCopiesSplit

namespace IBLP.FiniteBoundedData
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (D : FiniteBoundedData stage a)

include D in
/-- The original full-tail iteration has a fixed block width. Both the total
length and the last control predecessor are computed from the original input.
Only actual copy success is used; intermediate saturation is not assumed. -/
theorem rawCopies_length_control (proper : IBLP.ProperMarks a)
    {last : IBLP.Row} {p m : Nat} {b : IBLP.Pattern}
    (hlast : a.getLast? = some last) (hp : last.p = some p)
    (run : IBLP.rawCopies m a = some b) :
    b.length = a.length + m * (a.length - p) ∧
      ∃ next, b.getLast? = some next ∧ next.p = some (p + m * (a.length - p)) := by
  induction m generalizing stage a b last p with
  | zero =>
    have same : a = b := Option.some.inj run
    subst b
    exact ⟨by simp, last, hlast, by simpa using hp⟩
  | succ m ih =>
    obtain ⟨middle, first, rest⟩ := Option.bind_eq_some_iff.mp run
    have atLast := IBLP.getLast_rowAt hlast
    have nonempty := IBLP.rowAt_pos atLast
    have pred : IBLP.predecessor a a.length = some p := by
      simp [IBLP.predecessor, atLast, hp]
    have pn := IBLP.predecessor_lt D.valid D.shapes pred
    have headBound : 0 < last.columns.length := by
      have := (D.valid _ _ atLast).2.1
      omega
    let minimum := last.columns[0]'headBound
    have hm : last.columns.head? = some minimum := by
      simp only [List.head?_eq_getElem?, List.getElem?_eq_getElem headBound, minimum]
    obtain ⟨next, hnext, copiedNext⟩ := IBLP.rawCopy_last first hlast hp
    have hpNext := (D.copied_control nonempty atLast hm hp copiedNext).1
    let nextData := D.rawCopyData nonempty proper first hlast hm hp
    have nextProper := (D.rawCopy_geometry proper first).2.2
    obtain ⟨len, final, atFinal, finalP⟩ := ih nextData nextProper hnext hpNext rest
    have middleLength := IBLP.rawCopy_length first hlast hp
    have width : middle.length - a.length = a.length - p := by omega
    rw [width] at len finalP
    refine ⟨?_, final, atFinal, ?_⟩
    · rw [Nat.succ_mul]
      omega
    · convert finalP using 1; congr 1
      rw [Nat.succ_mul]
      omega

include D in
theorem rawCopies_block_width (proper : IBLP.ProperMarks a)
    {last next : IBLP.Row} {p q m : Nat} {b : IBLP.Pattern}
    (hlast : a.getLast? = some last) (hp : last.p = some p)
    (run : IBLP.rawCopies m a = some b)
    (hnext : b.getLast? = some next) (hq : next.p = some q) :
    b.length - q = a.length - p := by
  obtain ⟨len, final, atFinal, finalP⟩ := D.rawCopies_length_control proper hlast hp run
  have same : final = next := Option.some.inj (atFinal.symm.trans hnext)
  subst final
  have qeq := Option.some.inj (hq.symm.trans finalP)
  omega

end IBLP.FiniteBoundedData

namespace IBLP

/-- All repeated copies preserve the original strict prefix, including every
row below the first copied block. -/
theorem rawCopies_prefix {a b : Pattern} {m i : Nat}
    (run : rawCopies m a = some b) (before : i < a.length) : rowAt b i = rowAt a i := by
  induction m generalizing a b with
  | zero => exact congrArg (fun c => rowAt c i) (Option.some.inj run).symm
  | succ m ih =>
    obtain ⟨middle, first, rest⟩ := Option.bind_eq_some_iff.mp run
    exact (ih rest (before.trans_le (rawCopy_length_le first))).trans (rawCopy_prefix first before)

end IBLP

namespace IBLP.FiniteBoundedData
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (D : FiniteBoundedData stage a)

include D in
/-- Every earlier copy stage is recovered from the actual final run. Its
entire strict prefix persists, with the endpoint computed in original labels. -/
theorem rawCopies_stage_prefix (proper : IBLP.ProperMarks a)
    {last : IBLP.Row} {p m h : Nat} {b : IBLP.Pattern}
    (hlast : a.getLast? = some last) (hp : last.p = some p)
    (run : IBLP.rawCopies m a = some b) (within : h ≤ m) :
    ∃ middle, IBLP.rawCopies h a = some middle ∧
      middle.length = a.length + h * (a.length - p) ∧
      ∀ i, i < a.length + h * (a.length - p) → IBLP.rowAt b i = IBLP.rowAt middle i := by
  obtain ⟨middle, first, rest⟩ := IBLP.rawCopies_split run within
  have length := (D.rawCopies_length_control proper hlast hp first).1
  exact ⟨middle, first, length, fun _ before => IBLP.rawCopies_prefix rest (by omega)⟩

end IBLP.FiniteBoundedData
