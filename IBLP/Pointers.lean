import IBLP.Syntax

/-! 列表证明按 FullMarkedBLP/TraceCompute 与 NativeTermination（Apache-2.0）
移植；基本合法性与普通行型在本项目中分别假设。 -/
namespace IBLP

theorem rowAt_exists {a : Pattern} {r : Nat} (hr : 0 < r) (hb : r ≤ a.length) :
    ∃ row, rowAt a r = some row := by
  have hi : r - 1 < a.length := by omega
  refine ⟨a[r - 1], ?_⟩
  simp [rowAt, Nat.ne_of_gt hr, hi]

theorem rowAt_mem {a : Pattern} {r : Nat} {row : Row} (hr : rowAt a r = some row) : row ∈ a := by
  unfold rowAt at hr
  split at hr
  · simp at hr
  · obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp hr
    exact List.mem_iff_getElem.mpr ⟨r - 1, hi, he⟩

theorem fromRight_exists {xs : List Nat} {k : Nat} (hk : 0 < k) (hb : k ≤ xs.length) :
    ∃ v, fromRight xs k = some v := by
  have hi : xs.length - k < xs.length := by omega
  refine ⟨xs[xs.length - k], ?_⟩
  simp [fromRight, hk, hb, hi]

theorem fromRight_lt_last {xs : List Nat} {r k v : Nat}
    (hs : xs.Pairwise (· < ·)) (hl : xs.getLast? = some r)
    (hk : 1 < k) (hv : fromRight xs k = some v) : v < r := by
  unfold fromRight at hv
  split at hv
  · obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp hv
    rw [List.getLast?_eq_getElem?] at hl
    obtain ⟨hj, hf⟩ := List.getElem?_eq_some_iff.mp hl
    have hh := List.pairwise_iff_getElem.mp hs (xs.length - k)
      (xs.length - 1) hi hj (by omega)
    simpa [he, hf] using hh
  · simp at hv

theorem fromRight_pos {xs : List Nat} {k v : Nat}
    (hs : xs.Pairwise (· < ·)) (hk : 0 < k) (hb : k < xs.length)
    (hv : fromRight xs k = some v) : 0 < v := by
  have hx : k ≤ xs.length := by omega
  simp only [fromRight, hk, hx, and_self, ↓reduceIte] at hv
  obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp hv
  have hh := List.pairwise_iff_getElem.mp hs 0 (xs.length - k) (by omega) hi (by omega)
  rw [he] at hh
  omega

theorem fromRight_le_last {xs : List Nat} {r k v : Nat}
    (hs : xs.Pairwise (· < ·)) (hl : xs.getLast? = some r)
    (hk : 0 < k) (hv : fromRight xs k = some v) : v ≤ r := by
  by_cases he : k = 1
  · subst k
    unfold fromRight at hv
    split at hv
    · rw [← List.getLast?_eq_getElem?] at hv
      have hh := Option.some.inj (hv.symm.trans hl)
      omega
    · simp at hv
  · exact Nat.le_of_lt (fromRight_lt_last hs hl (by omega) hv)

theorem Row.step_pos {row : Row} (h : row.OrdinaryShape) : 0 < row.step := by
  rcases h with h | h | h <;> omega

theorem Row.step_lt_length {row : Row} (h : row.OrdinaryShape) : row.step < row.columns.length := by
  rcases h with h | h | h <;> omega

theorem Row.q_exists {r : Nat} {row : Row} (h : row.BasicValid r) :
    ∃ q, row.q = some q := fromRight_exists (by decide) h.2.1

theorem penultimate_lt {a : Pattern} (valid : BasicValid a)
    {r q : Nat} (hq : penultimate a r = some q) : q < r := by
  obtain ⟨row, hr, hq⟩ := Option.bind_eq_some_iff.mp hq
  have hv := valid r row hr
  exact fromRight_lt_last hv.1 hv.2.2.1 (by decide) hq

theorem predecessor_lt {a : Pattern} (valid : BasicValid a) (shapes : OrdinaryShape a)
    {r p : Nat} (hp : predecessor a r = some p) : p < r := by
  obtain ⟨row, hr, hp⟩ := Option.bind_eq_some_iff.mp hp
  have hv := valid r row hr
  have hs := Row.step_pos (shapes row (rowAt_mem hr))
  exact fromRight_lt_last hv.1 hv.2.2.1 (by omega) hp

end IBLP
