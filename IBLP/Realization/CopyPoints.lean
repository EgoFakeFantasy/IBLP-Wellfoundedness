import IBLP.Realization.BoundedRealization
import IBLP.Extender.ModelChange
import IBLP.Extender.RetainedPoints
import IBLP.Model.GraphCriticalAbsolute

namespace IBLP
open FullMarkedBLP Extender
universe u

namespace FiniteBoundedData
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (D : FiniteBoundedData stage a)

theorem point_top : D.point (a.length + 1) = D.top := by
  exact D.point_at ⟨a.length + 1, by omega⟩

def lastIndex (nonempty : 0 < a.length) : FiniteRowIndex a := ⟨a.length, nonempty, le_rfl⟩

noncomputable def lastDerivation (nonempty : 0 < a.length) :
    Derivation stage (D.source a.length) D.top where
  graph := D.graph (lastIndex nonempty)
  elementary := by
    rw [← D.point_top]
    exact D.elementary (lastIndex nonempty)

/-- The manuscript's extension is built from the actual last saved row. -/
noncomputable def lastExtension (nonempty : 0 < a.length) :
    InternalExtension (D.lastDerivation nonempty) :=
  (D.lastDerivation nonempty).extend (D.point_limit (rowEndpoint a a.length))
    (D.point_top ▸ D.point_limit (a.length + 1))
    (D.point_top ▸ D.point_inaccessible (a.length + 1))

theorem lastExtension_graph_value (nonempty : 0 < a.length) {x y : Nat}
    (edge : ZFSet.pair (D.point x).toZFSet (D.point y).toZFSet ∈
      (D.graph (lastIndex nonempty)).val) :
    stage.ordinalImage (D.lastExtension nonempty).embedding (D.point x) = D.point y := by
  obtain ⟨t, hx, hy⟩ := (D.lastDerivation nonempty).represents.graph_exact _ _ |>.mp edge
  have same := (D.lastExtension nonempty).agreement t
  have input : stage.rankInclude _ t = stage.ordinal (D.point x) := Subtype.ext hx
  rw [input] at same
  have equal : ((D.lastExtension nonempty).embedding (stage.ordinal (D.point x))).val =
      (D.point y).toZFSet := same.trans hy
  exact congrArg ZFSet.rank equal |>.trans (Ordinal.rank_toZFSet _)

theorem lastExtension_predecessor (nonempty : 0 < a.length) {p : Nat}
    (hp : predecessor a a.length = some p) :
    stage.ordinalImage (D.lastExtension nonempty).embedding (D.point p) = D.point a.length := by
  obtain ⟨row, hr, pred⟩ := Option.bind_eq_some_iff.mp hp
  exact D.lastExtension_graph_value nonempty (D.edges (lastIndex nonempty) row hr (p, a.length)
    (Row.predecessor_edge (D.valid _ _ hr) (D.shapes row (rowAt_mem hr)) pred))

/-- Old indices through n are retained; indices above n are the translated
elementary images. The shared index n is justified by the last p edge. -/
noncomputable def copyPoint (nonempty : 0 < a.length) (p i : Nat) : Ordinal.{u} :=
  if i ≤ a.length then D.point i else
    stage.ordinalImage (D.lastExtension nonempty).embedding (D.point (i - (a.length - p)))

theorem copyPoint_old (nonempty : 0 < a.length) (p i : Nat) (old : i ≤ a.length) :
    D.copyPoint nonempty p i = D.point i := if_pos old

theorem copyPoint_tail (nonempty : 0 < a.length) {p : Nat}
    (hp : predecessor a a.length = some p) (x : Nat) (tail : p ≤ x) :
    D.copyPoint nonempty p (x + (a.length - p)) =
      stage.ordinalImage (D.lastExtension nonempty).embedding (D.point x) := by
  have pn := predecessor_lt D.valid D.shapes hp
  by_cases equal : x = p
  · subst x
    have boundary : p + (a.length - p) = a.length := by omega
    rw [boundary, D.copyPoint_old nonempty p a.length le_rfl,
      D.lastExtension_predecessor nonempty hp]
  · rw [copyPoint, if_neg (by omega)]
    simp only [Nat.add_sub_cancel_right]

theorem copyPoint_increasing (nonempty : 0 < a.length) {p : Nat}
    (hp : predecessor a a.length = some p) :
    StrictMonoOn (D.copyPoint nonempty p) (Set.Iic (a.length + (a.length - p) + 1)) := by
  have pn := predecessor_lt D.valid D.shapes hp
  intro i hi k hk less
  change i ≤ a.length + (a.length - p) + 1 at hi
  change k ≤ a.length + (a.length - p) + 1 at hk
  by_cases oldk : k ≤ a.length
  · rw [D.copyPoint_old nonempty p i (by omega), D.copyPoint_old nonempty p k oldk]
    exact D.point_increasing (by change i ≤ a.length + 1; omega)
      (by change k ≤ a.length + 1; omega) less
  · simp only [copyPoint, if_neg oldk]
    by_cases oldi : i ≤ a.length
    · rw [if_pos oldi]
      apply lt_of_le_of_lt (D.point_increasing.monotoneOn
        (by change i ≤ a.length + 1; omega) (by change a.length ≤ a.length + 1; omega) oldi)
      rw [← D.lastExtension_predecessor nonempty hp]
      apply stage.ordinalImage_strictMono
      exact D.point_increasing (by change p ≤ a.length + 1; omega)
        (by change k - (a.length - p) ≤ a.length + 1; omega) (by omega)
    · rw [if_neg oldi]
      apply stage.ordinalImage_strictMono
      exact D.point_increasing (by change i - (a.length - p) ≤ a.length + 1; omega)
        (by change k - (a.length - p) ≤ a.length + 1; omega) (by omega)

theorem copyPoint_inaccessible (nonempty : 0 < a.length) (p i : Nat) :
    (D.lastExtension nonempty).next.model.InternalInaccessible
      ((D.lastExtension nonempty).next.ordinal (D.copyPoint nonempty p i)) := by
  by_cases old : i ≤ a.length
  · rw [D.copyPoint_old nonempty p i old]
    apply ((D.lastExtension nonempty).retained_inaccessible_iff
      (D.point_top ▸ D.point_limit (a.length + 1)) (D.point i) ?_).mpr (D.point_inaccessible i)
    rw [← D.point_top]
    exact D.point_increasing (by change i ≤ a.length + 1; omega)
      (by change a.length + 1 ≤ a.length + 1; omega) (by omega)
  · rw [copyPoint, if_neg old]
    have same : (D.lastExtension nonempty).embedding (stage.ordinal (D.point (i - (a.length - p)))) =
        (D.lastExtension nonempty).next.ordinal
          (stage.ordinalImage (D.lastExtension nonempty).embedding (D.point (i - (a.length - p)))) :=
      Subtype.ext (stage.ordinalImage_compat _ _)
    rw [← same]
    exact ((D.lastExtension nonempty).embedding.internalInaccessible_iff _).mpr (D.point_inaccessible _)

theorem copyPoint_top (nonempty : 0 < a.length) {p : Nat}
    (hp : predecessor a a.length = some p) :
    D.copyPoint nonempty p (a.length + (a.length - p) + 1) =
      stage.ordinalImage (D.lastExtension nonempty).embedding D.top := by
  have pn := predecessor_lt D.valid D.shapes hp
  have index : a.length + (a.length - p) + 1 = (a.length + 1) + (a.length - p) := by omega
  rw [index, D.copyPoint_tail nonempty hp (a.length + 1) (by omega), D.point_top]

end FiniteBoundedData
end IBLP
