import IBLP.Operations
import IBLP.Pointers

namespace IBLP

/-- 所有 q 跳转严格下降，所以 e+1 足够；不是任意的搜索上限。 -/
theorem nativeSourcesFuel_total {a : Pattern} (valid : BasicValid a)
    (p fuel : Nat) : ∀ u, 0 < u → u ≤ a.length → u < fuel →
    ∃ sources, nativeSourcesFuel a p fuel u = some sources := by
  induction fuel with
  | zero => intro u _ _ hf; omega
  | succ fuel ih =>
    intro u hu hb hf
    obtain ⟨row, hr⟩ := rowAt_exists hu hb
    obtain ⟨q, hq⟩ := Row.q_exists (valid u row hr)
    have hpen : penultimate a u = some q := by simp [penultimate, hr, hq]
    by_cases hp : p < q
    · have hd := penultimate_lt valid hpen
      obtain ⟨tail, ht⟩ := ih q (by omega) (by omega) (by omega)
      exact ⟨q :: tail, by simp [nativeSourcesFuel, hpen, hp, ht]⟩
    · exact ⟨[], by simp [nativeSourcesFuel, hpen, hp]⟩

theorem nativeSources_total {a : Pattern} (valid : BasicValid a) (shapes : OrdinaryShape a)
    {r : Nat} {row : Row} (hr : rowAt a r = some row) :
    ∃ sources, nativeSources a r = some sources := by
  have hv := valid r row hr
  have hs := shapes row (rowAt_mem hr)
  by_cases hlong : 2 * row.step < row.columns.length
  · exact ⟨[], by simp [nativeSources, hr, hlong]⟩
  · have hstep := Row.step_lt_length hs
    have hpos := Row.step_pos hs
    obtain ⟨p, hp⟩ := fromRight_exists (xs := row.columns) (k := row.step + 1) (by omega) (by omega)
    obtain ⟨e, he⟩ := fromRight_exists (xs := row.columns) (k := row.step) hpos (by omega)
    have hepos := fromRight_pos hv.1 hpos hstep he
    have heb := fromRight_le_last hv.1 hv.2.2.1 hpos he
    have hrb := rowAt_le_length hr
    obtain ⟨ss, hh⟩ := nativeSourcesFuel_total valid p (e + 1) e hepos (by omega) (by omega)
    exact ⟨ss, by simp [nativeSources, hr, hlong, Row.p, Row.e, hp, he, hh]⟩

theorem nativeSourcesFuel_bounds {a : Pattern} (valid : BasicValid a)
    {p fuel u : Nat} {sources : List Nat} (h : nativeSourcesFuel a p fuel u = some sources) :
    ∀ x ∈ sources, p < x ∧ x < u := by
  induction fuel generalizing u sources with
  | zero => simp [nativeSourcesFuel] at h
  | succ fuel ih =>
    obtain ⟨q, hq, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · rename_i hp
      obtain ⟨tail, ht, h⟩ := Option.bind_eq_some_iff.mp h
      change some (q :: tail) = some sources at h
      cases Option.some.inj h
      have hd := penultimate_lt valid hq
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨hp, hd⟩
      · have hi := ih ht x hx
        exact ⟨hi.1, hi.2.trans hd⟩
    · change some [] = some sources at h
      cases Option.some.inj h
      simp

theorem nativeSourcesFuel_decreasing {a : Pattern} (valid : BasicValid a)
    {p fuel u : Nat} {sources : List Nat} (h : nativeSourcesFuel a p fuel u = some sources) :
    sources.Pairwise (· > ·) := by
  induction fuel generalizing u sources with
  | zero => simp [nativeSourcesFuel] at h
  | succ fuel ih =>
    obtain ⟨q, _, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · obtain ⟨tail, ht, h⟩ := Option.bind_eq_some_iff.mp h
      change some (q :: tail) = some sources at h
      cases Option.some.inj h
      exact List.pairwise_cons.mpr
        ⟨fun x hx => (nativeSourcesFuel_bounds valid ht x hx).2, ih ht⟩
    · change some [] = some sources at h
      cases Option.some.inj h
      exact List.Pairwise.nil

end IBLP
