/- 移植自 FullMarkedBLP/ScanTermination.lean（Apache-2.0）。改为原 IBLP 的数据、冻结队列及任意扫描入口；所有证明重新由本项目编译。 -/
import IBLP.Operations

namespace IBLP

theorem rowAt_bounds {a : Pattern} {r : Nat} {row : Row}
    (h : rowAt a r = some row) : 0 < r ∧ r ≤ a.length := by
  unfold rowAt at h
  split at h
  next => simp at h
  next hn =>
    obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp h
    omega

theorem nativeBlockDown_length {k owner : Nat} {medium : Bool}
    {top : Row} {block : Pattern}
    (h : nativeBlockDown k owner medium top = some block) : block.length = k + 1 := by
  induction k generalizing owner medium top block with
  | zero => simp [nativeBlockDown] at h; subst block; rfl
  | succ k ih =>
    obtain ⟨lower, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨earlier, he, h⟩ := Option.bind_eq_some_iff.mp h
    change some (earlier ++ [top]) = some block at h
    cases Option.some.inj h
    simp [ih he]

theorem nativeBlock_length {row : Row} {r : Nat} {sources : List Nat} {block : Pattern}
    (h : nativeBlock row r sources = some block) : block.length = sources.length + 1 := by
  unfold nativeBlock at h
  split at h
  next he =>
    have hs : sources = [] := List.isEmpty_iff.mp he
    subst sources
    cases Option.some.inj h
    rfl
  next => exact nativeBlockDown_length h

theorem native_length {a b : Pattern} {r : Nat} {sources : List Nat}
    (h : native a r = some (b, sources)) : b.length = a.length + sources.length := by
  obtain ⟨row, hr, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨ss, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨block, hb, h⟩ := Option.bind_eq_some_iff.mp h
  change some (_, ss) = some (b, sources) at h
  have he := Option.some.inj h
  cases he
  have hh := nativeBlock_length hb
  have hi := rowAt_bounds hr
  simp only [List.length_append, List.length_take, List.length_map, List.length_drop]
  omega

theorem completeMark_length (a : Pattern) (rec : Records) (r y : Nat) :
    (completeMark a rec r y).length = a.length := by
  unfold completeMark
  split <;> simp

theorem completeMarks_fold_length (marks : List Nat) (a : Pattern) (rec : Records) (r : Nat) :
    (marks.foldl (fun current y => completeMark current rec r y) a).length = a.length := by
  induction marks generalizing a with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.foldl_cons]
    rw [ih, completeMark_length]

theorem completeFrozenMarks_length (a : Pattern) (rec : Records) (r : Nat) :
    (completeFrozenMarks a rec r).length = a.length := by
  unfold completeFrozenMarks
  split
  · rfl
  · exact completeMarks_fold_length _ _ _ _

/-- A successful scan event decreases the number of old rows remaining by one. -/
theorem scan_remaining_decreases {a b : Pattern} {rec : Records} {r : Nat}
    {sources : List Nat} (hb : r ≤ a.length)
    (h : native (completeFrozenMarks a rec r) r = some (b, sources)) :
    b.length + 1 - (r + sources.length + 1) + 1 = a.length + 1 - r := by
  have hl := native_length h
  rw [completeFrozenMarks_length] at hl
  omega


/-- Unbudgeted finite execution, used to prove the implementation bound exact. -/
inductive ScanRun : Pattern → Records → Nat → Pattern → Prop
  | done {a rec r} : a.length < r → ScanRun a rec r a
  | next {a b result rec r sources} : r ≤ a.length →
      native (completeFrozenMarks a rec r) r = some (b, sources) →
      ScanRun b (if sources.isEmpty then rec else (r, sources) :: rec)
        (r + sources.length + 1) result → ScanRun a rec r result

theorem scanFuel_sound {fuel : Nat} {a result : Pattern} {rec : Records} {r : Nat}
    (h : scanFuel fuel a rec r = some result) : ScanRun a rec r result := by
  induction fuel generalizing a rec r with
  | zero =>
    simp only [scanFuel] at h
    split at h
    next hr => cases Option.some.inj h; exact ScanRun.done hr
    next => simp at h
  | succ fuel ih =>
    simp only [scanFuel] at h
    split at h
    next hr => cases Option.some.inj h; exact ScanRun.done hr
    next hr =>
      obtain ⟨⟨b, sources⟩, hb, h⟩ := Option.bind_eq_some_iff.mp h
      exact ScanRun.next (by omega) hb (ih h)

theorem scanFuel_complete {a result : Pattern} {rec : Records} {r : Nat}
    (h : ScanRun a rec r result) : ∀ fuel, a.length + 1 - r ≤ fuel →
    scanFuel fuel a rec r = some result := by
  induction h with
  | done hr =>
    intro fuel _
    cases fuel <;> simp [scanFuel, hr]
  | @next a b result rec r sources hr hn ht ih =>
    intro fuel hf
    have hd := scan_remaining_decreases hr hn
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hh := ih fuel (by omega)
      simp only [scanFuel, Nat.not_lt.mpr hr, ↓reduceIte]
      rw [hn]
      exact hh

theorem scan_iff {a result : Pattern} {start : Nat} :
    scan a start = some result ↔ ScanRun a [] start result := by
  constructor
  · exact scanFuel_sound
  · intro h
    exact scanFuel_complete h _ (by omega)

end IBLP

