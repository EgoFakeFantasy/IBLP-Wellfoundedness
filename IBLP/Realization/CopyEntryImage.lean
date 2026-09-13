import IBLP.CopyEntry
import IBLP.Realization.CopyPoints

namespace IBLP.FiniteBoundedData
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (D : FiniteBoundedData stage a)

theorem lastExtension_fixes_low (nonempty : 0 < a.length) {last : IBLP.Row} {minimum x : Nat}
    (hr : rowAt a a.length = some last) (hm : last.columns.head? = some minimum)
    (low : x < minimum) :
    stage.ordinalImage (D.lastExtension nonempty).embedding (D.point x) = D.point x := by
  have critical := D.critical (lastIndex nonempty) last minimum hr hm
  have hc : D.point minimum ≤ D.source a.length := by
    obtain ⟨y, edge, _⟩ := critical.2.1
    have dom := (ZFSet.pair_mem_prod.mp ((D.lastDerivation nonempty).represents.1.1
      ((stage.model.graphApplies_absolute _ _ _).mp edge))).1
    exact Order.le_of_lt_succ ((stage.ordinal_mem_hierarchy _ _).mp dom)
  have hmem : minimum ∈ last.columns := by
    obtain ⟨bound, value⟩ := List.getElem?_eq_some_iff.mp
      (show last.columns[0]? = some minimum by simpa only [List.head?_eq_getElem?] using hm)
    exact List.mem_iff_getElem.mpr ⟨0, bound, value⟩
  have mn := Row.column_le_last (D.valid _ _ hr) hmem
  have small := D.point_increasing (by change x ≤ a.length + 1; omega)
    (by change minimum ≤ a.length + 1; omega) low
  have fixed := ((D.lastExtension nonempty).critical_agrees (D.point minimum) hc critical).2
    (D.point x) small
  exact congrArg ZFSet.rank fixed |>.trans (Ordinal.rank_toZFSet _)

/-- All three program branches realize the elementary image on the spliced
point list, including every point in the full translated tail. -/
theorem copyEntry_image (nonempty : 0 < a.length) {last : IBLP.Row} {minimum p x y : Nat}
    (hr : rowAt a a.length = some last) (hm : last.columns.head? = some minimum)
    (hp : last.p = some p)
    (copied : copyEntry a.length last x = some y) :
    D.copyPoint nonempty p y =
      stage.ordinalImage (D.lastExtension nonempty).embedding (D.point x) := by
  have pred : predecessor a a.length = some p := by simp [predecessor, hr, hp]
  rcases copyEntry_cases hm hp copied with ⟨low, equal⟩ | ⟨_, tail, equal⟩ | ⟨_, _, edge⟩
  · subst y
    have hmem : minimum ∈ last.columns := by
      obtain ⟨hm0, he0⟩ := List.getElem?_eq_some_iff.mp
        (show last.columns[0]? = some minimum by simpa only [List.head?_eq_getElem?] using hm)
      exact List.mem_iff_getElem.mpr ⟨0, hm0, he0⟩
    have mn := Row.column_le_last (D.valid _ _ hr) hmem
    rw [D.copyPoint_old nonempty p x (by omega), D.lastExtension_fixes_low nonempty hr hm low]
  · subst y
    exact D.copyPoint_tail nonempty pred x tail
  · have yn := Row.column_le_last (D.valid _ _ hr)
      (List.mem_of_mem_drop (List.of_mem_zip edge).2)
    rw [D.copyPoint_old nonempty p y yn]
    exact (D.lastExtension_graph_value nonempty
      (D.edges (lastIndex nonempty) last hr (x, y) (Row.explicit_edge edge))).symm

include D in
/-- Successful entries are strictly ordered as actual indices. Consequently
sorting the copied columns cannot identify or reorder valid source columns. -/
theorem copyEntry_strict (nonempty : 0 < a.length) {last : IBLP.Row}
    {minimum p x y fx fy : Nat} (hr : rowAt a a.length = some last)
    (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (hy : y ≤ a.length + 1) (less : x < y)
    (hximage : copyEntry a.length last x = some fx)
    (hyimage : copyEntry a.length last y = some fy) : fx < fy := by
  have hx : x ≤ a.length + 1 := by omega
  have pred : predecessor a a.length = some p := by simp [predecessor, hr, hp]
  have fxb := copyEntry_bound (D.valid _ _ hr) hm hp hx hximage
  have fyb := copyEntry_bound (D.valid _ _ hr) hm hp hy hyimage
  have values : D.copyPoint nonempty p fx < D.copyPoint nonempty p fy := by
    rw [D.copyEntry_image nonempty hr hm hp hximage, D.copyEntry_image nonempty hr hm hp hyimage]
    exact stage.ordinalImage_strictMono _ (D.point_increasing hx hy less)
  by_contra bad
  have reverse := (D.copyPoint_increasing nonempty pred).monotoneOn fyb fxb (by omega)
  exact (not_lt_of_ge reverse) values

end IBLP.FiniteBoundedData
