import IBLP.Pointers
import IBLP.Realization.InternalTraceRows

namespace IBLP
open FullMarkedBLP
universe u

theorem fromRight_lt_fromRight {xs : List Nat} {k l x y : Nat}
    (ordered : xs.Pairwise (· < ·)) (indices : l < k)
    (hx : fromRight xs k = some x) (hy : fromRight xs l = some y) : x < y := by
  unfold fromRight at hx hy
  split at hx
  · rename_i hk
    split at hy
    · rename_i hl
      obtain ⟨ix, ex⟩ := List.getElem?_eq_some_iff.mp hx
      obtain ⟨iy, ey⟩ := List.getElem?_eq_some_iff.mp hy
      have h := List.pairwise_iff_getElem.mp ordered (xs.length - k) (xs.length - l)
        ix iy (by omega)
      simpa only [ex, ey] using h
    · simp at hy
  · simp at hx

theorem Row.predecessor_lt_endpoint {r p e : Nat} {row : Row} (valid : row.BasicValid r)
    (hp : row.p = some p) (he : row.e = some e) : p < e :=
  fromRight_lt_fromRight valid.1 (Nat.lt_succ_self row.step) hp he

/-- The source endpoint is read from the original row, and exists whenever a
valid ordinary row supplies the p edge used by the trace. -/
theorem predecessor_endpoint_exists {a : Pattern} (valid : BasicValid a) (shapes : OrdinaryShape a)
    {r p : Nat} (hp : predecessor a r = some p) :
    ∃ row e, rowAt a r = some row ∧ row.e = some e ∧ p < e ∧ e ≤ r := by
  obtain ⟨row, hr, hp⟩ := Option.bind_eq_some_iff.mp hp
  have ordinary := shapes row (rowAt_mem hr)
  obtain ⟨e, he⟩ := fromRight_exists (Row.step_pos ordinary) (Row.step_lt_length ordinary).le
  exact ⟨row, e, hr, he, Row.predecessor_lt_endpoint (valid r row hr) hp he,
    fromRight_le_last (valid r row hr).1 (valid r row hr).2.2.1 (Row.step_pos ordinary) he⟩

/-- Only the finite theta sequence through n+1 is required to be increasing. -/
theorem predecessor_source_bounds {a : Pattern} (valid : BasicValid a) (shapes : OrdinaryShape a)
    {theta source : Nat → Ordinal.{u}}
    (increasing : StrictMonoOn theta (Set.Iic (a.length + 1)))
    (source_eq : ∀ r row e, rowAt a r = some row → row.e = some e → source r = theta e)
    {r p : Nat} (hp : predecessor a r = some p) :
    theta p < source r ∧ theta (p + 1) ≤ source r := by
  obtain ⟨row, e, hr, he, hpe, her⟩ := predecessor_endpoint_exists valid shapes hp
  have rb := rowAt_le_length hr
  have eb : e ≤ a.length + 1 := by omega
  have pb : p ≤ a.length + 1 := by omega
  have psb : p + 1 ≤ a.length + 1 := by omega
  rw [source_eq r row e hr he]
  refine ⟨increasing pb eb hpe, ?_⟩
  exact increasing.monotoneOn psb eb (by omega)

namespace InternalTraceRows

/-- Construct the row interface from original p/e geometry. Both domain
inequalities are proved from the original arrays and finite theta order. -/
noncomputable def ofPattern (stage : ModelStage.{u}) (a : Pattern) (theta source : Nat → Ordinal.{u})
    (valid : BasicValid a) (shapes : OrdinaryShape a)
    (increasing : StrictMonoOn theta (Set.Iic (a.length + 1)))
    (source_eq : ∀ r row e, rowAt a r = some row → row.e = some e → source r = theta e)
    (limits : ∀ r, Order.IsSuccLimit (source r))
    (maps : ∀ r, stage.BoundedMap (source r) (theta (r + 1)))
    (edges : ∀ r p, (hp : predecessor a r = some p) →
      (maps r (stage.rankOrdinal ⟨theta p,
        Order.lt_succ_of_le (predecessor_source_bounds valid shapes increasing source_eq hp).1.le⟩)).val =
        (theta r).toZFSet) : InternalTraceRows stage a theta where
  source := source
  source_limit := limits
  map := maps
  source_gap := fun _ _ hp => (predecessor_source_bounds valid shapes increasing source_eq hp).1
  adjacent_domain := fun _ _ hp => (predecessor_source_bounds valid shapes increasing source_eq hp).2
  predecessor_value := edges

end InternalTraceRows
end IBLP
