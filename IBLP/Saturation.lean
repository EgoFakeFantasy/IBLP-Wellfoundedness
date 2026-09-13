import IBLP.NativeStrongClosure
import FullMarkedBLP.ScanSat

namespace IBLP

/-- Saturation for the already processed prefix; the bound is the first
unprocessed row and new native families are included before advancing it. -/
def SaturatedBefore (a : Pattern) (bound : Nat) : Prop :=
  ∀ r row p e q, r < bound → rowAt a r = some row → row.p = some p → row.e = some e →
    penultimate a e = some q → q ≤ p

theorem Saturated.before {a : Pattern} (saturated : Saturated a) (bound : Nat) : SaturatedBefore a bound :=
  fun r row p e q _ => saturated r row p e q

theorem SaturatedBefore.all {a : Pattern} {bound : Nat} (saturated : SaturatedBefore a bound)
    (endReached : a.length < bound) : Saturated a := by
  intro r row p e q hr hp he hq
  exact saturated r row p e q (by have := rowAt_le_length hr; omega) hr hp he hq

theorem Row.step_one_saturated {a : Pattern} {r p e q : Nat} {row : Row}
    (valid : row.BasicValid r) (hr : rowAt a r = some row) (step : row.step = 1)
    (hp : row.p = some p) (he : row.e = some e) (hq : penultimate a e = some q) : q ≤ p := by
  have endpoint : e = r := by
    have len := valid.2.1
    have eq : row.columns.getLast? = some e := by
      simpa only [Row.e, step, fromRight,
        show 0 < 1 ∧ 1 ≤ row.columns.length by omega, if_true,
        ← List.getLast?_eq_getElem?] using he
    exact Option.some.inj (eq.symm.trans valid.2.2.1)
  subst e
  have same : row.q = row.p := by simp only [Row.q, Row.p, step]
  simp only [penultimate, hr, Option.bind_some, same, hp, Option.some.injEq] at hq
  omega

namespace NativeBridge

/-- The upstream witness form and the original q≤p form agree on valid
original rows. The extra three-column shape is checked separately. -/
theorem saturatedBefore_encode {a : Pattern} {bound : Nat} (valid : BasicValid a)
    (shapes : OrdinaryShape a) (sat : SaturatedBefore a bound) : FullMarkedBLP.SatBelow (encode a) bound := by
  intro i out before atOut _
  rw [rowAt_encode] at atOut
  obtain ⟨row, hr, eq⟩ := Option.map_eq_some_iff.mp atOut
  subst out
  have hv := valid _ _ hr
  have hs := shapes row (rowAt_mem hr)
  obtain ⟨p, hp⟩ := fromRight_exists (xs := row.columns) (k := row.step + 1)
    (by omega) (by have := Row.step_lt_length hs; omega)
  obtain ⟨e, he⟩ := fromRight_exists (xs := row.columns) (Row.step_pos hs) (Row.step_lt_length hs).le
  have ep := fromRight_pos hv.1 (Row.step_pos hs) (Row.step_lt_length hs) he
  have eb := fromRight_le_last hv.1 hv.2.2.1 (Row.step_pos hs) he
  obtain ⟨er, atEr⟩ := rowAt_exists ep (eb.trans (rowAt_le_length hr))
  obtain ⟨q, hq⟩ := Row.q_exists (valid _ _ atEr)
  have pen : penultimate a e = some q := by simp only [penultimate, atEr, Option.bind_some, hq]
  exact ⟨p, e, encodeRow er, q, hp, he, by simp only [rowAt_encode, atEr, Option.map_some],
    hq, sat i row p e q before hr hp he pen⟩

theorem saturatedBefore_of_encode {a : Pattern} {bound : Nat} (valid : BasicValid a)
    (shapes : OrdinaryShape a) (sat : FullMarkedBLP.SatBelow (encode a) bound) : SaturatedBefore a bound := by
  intro i row p e q before hr hp he hq
  by_cases eligible : row.columns.length ≤ 2 * row.step
  · have atEncoded : FullMarkedBLP.rowAt (encode a) i = some (encodeRow row) := by simp only [rowAt_encode, hr, Option.map_some]
    obtain ⟨p', e', er, q', hp', he', atEr, hq', le⟩ := sat i (encodeRow row) before atEncoded eligible
    have pp : p' = p := Option.some.inj (hp'.symm.trans hp)
    have ee : e' = e := Option.some.inj (he'.symm.trans he)
    subst p'; subst e'
    rw [rowAt_encode] at atEr
    obtain ⟨actual, atActual, same⟩ := Option.map_eq_some_iff.mp atEr
    subst er
    have pen : penultimate a e = some q' := by simp only [penultimate, atActual, Option.bind_some]; exact hq'
    have qq := Option.some.inj (pen.symm.trans hq)
    omega
  · have shape := shapes row (rowAt_mem hr)
    have step : row.step = 1 := by rcases shape with h | h | h <;> omega
    exact Row.step_one_saturated (valid _ _ hr) hr step hp he hq

end NativeBridge

/-- Native establishes saturation for its complete family and preserves
all previously processed rows, without assuming saturation above the cursor. -/
theorem native_advances_saturation {a b : Pattern} (valid : BasicValid a) (shapes : OrdinaryShape a)
    (proper : ProperMarks a) {r : Nat} {sources : List Nat} (before : SaturatedBefore a r)
    (run : native a r = some (b, sources)) : SaturatedBefore b (r + sources.length + 1) := by
  have output := native_preserves_syntax valid shapes proper run
  exact NativeBridge.saturatedBefore_of_encode output.1 output.2.1
    (FullMarkedBLP.native_advances_sat_prefix (NativeBridge.valid_encode valid shapes)
      (NativeBridge.saturatedBefore_encode valid shapes before) ((NativeBridge.native_encode a r).trans (by simp only [run, Option.map_some])))

end IBLP
