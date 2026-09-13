import IBLP.Realization.InternalTraceRows
import IBLP.Realization.BoundedMapGraph

namespace IBLP
open FullMarkedBLP FirstOrder Language
universe u

/-- The only stored row numbers are the manuscript's one-based rows. -/
abbrev FiniteRowIndex (a : Pattern) := {r : Nat // 0 < r ∧ r ≤ a.length}

/-- The auxiliary infinite indexing is a canonical extension of n+2 points. -/
def finiteThetaExtension {n : Nat} (theta : Fin (n + 2) → Ordinal.{u}) (r : Nat) : Ordinal.{u} :=
  theta ⟨min r (n + 1), by omega⟩

theorem finiteThetaExtension_at {n : Nat} (theta : Fin (n + 2) → Ordinal.{u})
    (r : Fin (n + 2)) : finiteThetaExtension theta r.val = theta r := by
  unfold finiteThetaExtension
  congr 1
  apply Fin.ext
  exact min_eq_left (by omega)

theorem finiteThetaExtension_strictMonoOn {n : Nat} (theta : Fin (n + 2) → Ordinal.{u})
    (increasing : StrictMono theta) : StrictMonoOn (finiteThetaExtension theta) (Set.Iic (n + 1)) := by
  intro x hx y hy smaller
  change x ≤ n + 1 at hx
  change y ≤ n + 1 at hy
  apply increasing
  change min x (n + 1) < min y (n + 1)
  simpa only [min_eq_left hx, min_eq_left hy] using smaller

theorem predecessor_row_index {a : Pattern} {r p : Nat} (hp : predecessor a r = some p) :
    0 < r ∧ r ≤ a.length := by
  obtain ⟨row, hr, _⟩ := Option.bind_eq_some_iff.mp hp
  exact ⟨rowAt_pos hr, rowAt_le_length hr⟩

/-- All hypotheses are finite: n+2 endpoint ordinals, and one map and its
local p-edge facts for each of the n actual rows. -/
structure FiniteTraceRows (stage : ModelStage.{u}) (a : Pattern)
    (theta : Fin (a.length + 2) → Ordinal.{u}) where
  theta_limit : ∀ i, Order.IsSuccLimit (theta i)
  source : FiniteRowIndex a → Ordinal.{u}
  source_limit : ∀ r, Order.IsSuccLimit (source r)
  map : ∀ r, stage.BoundedMap (source r) (finiteThetaExtension theta (r.val + 1))
  source_gap : ∀ r p, predecessor a r.val = some p → finiteThetaExtension theta p < source r
  adjacent_domain : ∀ r p, predecessor a r.val = some p →
    finiteThetaExtension theta (p + 1) ≤ source r
  predecessor_value : ∀ r p, (hp : predecessor a r.val = some p) →
    (map r (stage.rankOrdinal ⟨finiteThetaExtension theta p,
      Order.lt_succ_of_le (source_gap r p hp).le⟩)).val = (finiteThetaExtension theta r.val).toZFSet

namespace FiniteTraceRows
variable {stage : ModelStage.{u}} {a : Pattern} {theta : Fin (a.length + 2) → Ordinal.{u}}

/-- Missing row indices use an identity map whose source equals its target.
This is a definition from finite data, never an additional infinite family. -/
noncomputable def extendedRow (R : FiniteTraceRows stage a theta) (r : Nat) :
    Σ alpha : Ordinal.{u}, stage.BoundedMap alpha (finiteThetaExtension theta (r + 1)) :=
  if hr : 0 < r ∧ r ≤ a.length then ⟨R.source ⟨r, hr⟩, R.map ⟨r, hr⟩⟩
  else ⟨finiteThetaExtension theta (r + 1), ElementaryEmbedding.refl membershipLanguage _⟩

theorem extendedRow_valid (R : FiniteTraceRows stage a theta) (r : FiniteRowIndex a) :
    R.extendedRow r.val = ⟨R.source r, R.map r⟩ := by
  simp only [extendedRow, dif_pos r.property]

theorem extendedRow_invalid (R : FiniteTraceRows stage a theta) (r : Nat)
    (hr : ¬(0 < r ∧ r ≤ a.length)) :
    R.extendedRow r = ⟨finiteThetaExtension theta (r + 1), ElementaryEmbedding.refl membershipLanguage _⟩ := by
  simp only [extendedRow, dif_neg hr]

theorem extendedRow_predecessor_value (R : FiniteTraceRows stage a theta) (r p : Nat)
    (hp : predecessor a r = some p) (bound : finiteThetaExtension theta p < (R.extendedRow r).1) :
    ((R.extendedRow r).2 (stage.rankOrdinal
      ⟨finiteThetaExtension theta p, Order.lt_succ_of_le bound.le⟩)).val =
      (finiteThetaExtension theta r).toZFSet := by
  have hr := predecessor_row_index hp
  have general (row : Σ alpha : Ordinal.{u}, stage.BoundedMap alpha (finiteThetaExtension theta (r + 1)))
      (same : row = ⟨R.source ⟨r, hr⟩, R.map ⟨r, hr⟩⟩)
      (hb : finiteThetaExtension theta p < row.1) :
      (row.2 (stage.rankOrdinal ⟨finiteThetaExtension theta p, Order.lt_succ_of_le hb.le⟩)).val =
        (finiteThetaExtension theta r).toZFSet := by
    subst row
    exact R.predecessor_value ⟨r, hr⟩ p hp
  exact general _ (R.extendedRow_valid ⟨r, hr⟩) bound

noncomputable def toInternalTraceRows (R : FiniteTraceRows stage a theta) :
    InternalTraceRows stage a (finiteThetaExtension theta) where
  source := fun r => (R.extendedRow r).1
  source_limit := by
    intro r
    by_cases hr : 0 < r ∧ r ≤ a.length
    · simpa only [extendedRow, dif_pos hr] using R.source_limit ⟨r, hr⟩
    · simpa only [extendedRow, dif_neg hr] using R.theta_limit ⟨min (r + 1) (a.length + 1), by omega⟩
  map := fun r => (R.extendedRow r).2
  source_gap := by
    intro r p hp
    have hr := predecessor_row_index hp
    simpa only [extendedRow, dif_pos hr] using R.source_gap ⟨r, hr⟩ p hp
  adjacent_domain := by
    intro r p hp
    have hr := predecessor_row_index hp
    simpa only [extendedRow, dif_pos hr] using R.adjacent_domain ⟨r, hr⟩ p hp
  predecessor_value := by
    intro r p hp
    apply R.extendedRow_predecessor_value r p hp
    have hr := predecessor_row_index hp
    simpa only [extendedRow, dif_pos hr] using R.source_gap ⟨r, hr⟩ p hp

theorem source_valid (R : FiniteTraceRows stage a theta) (r : FiniteRowIndex a) :
    R.toInternalTraceRows.source r.val = R.source r := by
  change (R.extendedRow r.val).1 = R.source r
  rw [R.extendedRow_valid]

theorem source_invalid (R : FiniteTraceRows stage a theta) (r : Nat)
    (hr : ¬(0 < r ∧ r ≤ a.length)) :
    R.toInternalTraceRows.source r = finiteThetaExtension theta (r + 1) := by
  change (R.extendedRow r).1 = _
  rw [R.extendedRow_invalid r hr]

/-- Valid rows retain every original map value; only the rank-membership
proofs differ between the finite and extended interfaces. -/
theorem map_valid_value (R : FiniteTraceRows stage a theta) (r : FiniteRowIndex a)
    (x : stage.model.RankElement (Order.succ (R.source r)))
    (y : stage.model.RankElement (Order.succ (R.toInternalTraceRows.source r.val)))
    (same : y.val = x.val) : (R.toInternalTraceRows.map r.val y).val = (R.map r x).val := by
  have general (row : Σ alpha : Ordinal.{u}, stage.BoundedMap alpha (finiteThetaExtension theta (r.val + 1)))
      (rowEq : row = ⟨R.source r, R.map r⟩)
      (input : stage.model.RankElement (Order.succ row.1)) (sameInput : input.val = x.val) :
      (row.2 input).val = (R.map r x).val := by
    subst row
    have inputEq : input = x := Subtype.ext sameInput
    rw [inputEq]
  exact general _ (R.extendedRow_valid r) y same

theorem represents_valid (R : FiniteTraceRows stage a theta) (r : FiniteRowIndex a)
    (graph : stage.model.Element) (represents : stage.RepresentsBoundedMap graph (R.map r)) :
    stage.RepresentsBoundedMap graph (R.toInternalTraceRows.map r.val) := by
  change stage.RepresentsBoundedMap graph (R.extendedRow r.val).2
  rw [R.extendedRow_valid]
  exact represents

/-- Only the finite graph witnesses are required for genuine rows. -/
theorem graph_valid_exists (R : FiniteTraceRows stage a theta)
    (graphs : ∀ r : FiniteRowIndex a, ∃ graph : stage.model.Element,
      stage.RepresentsBoundedMap graph (R.map r)) (r : FiniteRowIndex a) :
    ∃ graph : stage.model.Element, stage.RepresentsBoundedMap graph (R.toInternalTraceRows.map r.val) := by
  obtain ⟨graph, hg⟩ := graphs r
  exact ⟨graph, R.represents_valid r graph hg⟩

end FiniteTraceRows

theorem FactorTrace.validRows {a : Pattern} {target start : Nat} {rows : List Nat}
    (h : FactorTrace a target start rows) : ∀ r ∈ rows, 0 < r ∧ r ≤ a.length := by
  induction h with
  | single hp hn =>
    intro r hr
    have same := List.mem_singleton.mp hr
    subst r
    exact predecessor_row_index hp
  | cons hp hn inner ih =>
    intro r hr
    rcases List.mem_cons.mp hr with same | member
    · subst r
      exact predecessor_row_index hp
    · exact ih r member

/-- The actual factors of any trace obtain graph witnesses from the finite
row family. No graph assumption is made at unused Nat indices. -/
theorem FiniteTraceRows.graphs_on_trace {stage : ModelStage.{u}} {a : Pattern}
    {theta : Fin (a.length + 2) → Ordinal.{u}} (R : FiniteTraceRows stage a theta)
    (graphs : ∀ r : FiniteRowIndex a, ∃ graph : stage.model.Element,
      stage.RepresentsBoundedMap graph (R.map r))
    {target start : Nat} {rows : List Nat} (h : FactorTrace a target start rows) :
    ∀ r ∈ rows, ∃ graph : stage.model.Element,
      stage.RepresentsBoundedMap graph (R.toInternalTraceRows.map r) := by
  intro r hr
  exact R.graph_valid_exists graphs ⟨r, h.validRows r hr⟩

end IBLP
