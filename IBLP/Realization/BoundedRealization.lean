import IBLP.Realization.RowGeometry
import IBLP.Realization.MarkCertificate
import IBLP.Model.GraphCriticalPoint

namespace IBLP
open FullMarkedBLP
universe u

/-- Finite data for manuscript (3.1)--(3.3). The graphs are actual sets of M;
their elementary maps are recovered from these sets, not supplied by owners. -/
structure FiniteBoundedData (stage : ModelStage.{u}) (a : Pattern) where
  theta : Fin (a.length + 2) → Ordinal.{u}
  increasing : StrictMono theta
  inaccessible : ∀ i, stage.model.InternalInaccessible (stage.ordinal (theta i))
  valid : BasicValid a
  shapes : OrdinaryShape a
  graph : FiniteRowIndex a → stage.model.Element
  elementary : ∀ r, stage.InternalGraphElementary
    (finiteThetaExtension theta (rowEndpoint a r.val))
    (finiteThetaExtension theta (r.val + 1)) (graph r)
  critical : ∀ r row minimum, rowAt a r.val = some row → row.columns.head? = some minimum →
    stage.model.GraphCriticalPoint (graph r) (stage.ordinal (finiteThetaExtension theta minimum))
  edges : ∀ r row, rowAt a r.val = some row → ∀ edge ∈ row.edgePairs r.val,
    ZFSet.pair (finiteThetaExtension theta edge.1).toZFSet
      (finiteThetaExtension theta edge.2).toZFSet ∈ (graph r).val

namespace FiniteBoundedData
variable {stage : ModelStage.{u}} {a : Pattern} (D : FiniteBoundedData stage a)

def top : Ordinal.{u} := D.theta ⟨a.length + 1, by omega⟩

def point (r : Nat) : Ordinal.{u} := finiteThetaExtension D.theta r

theorem point_at (r : Fin (a.length + 2)) : D.point r.val = D.theta r :=
  finiteThetaExtension_at D.theta r

theorem point_increasing : StrictMonoOn D.point (Set.Iic (a.length + 1)) :=
  finiteThetaExtension_strictMonoOn D.theta D.increasing

theorem point_inaccessible (r : Nat) :
    stage.model.InternalInaccessible (stage.ordinal (D.point r)) :=
  D.inaccessible ⟨min r (a.length + 1), by omega⟩

theorem point_limit (r : Nat) : Order.IsSuccLimit (D.point r) := by
  have limit := stage.internalInaccessible_isSuccLimit _ (D.point_inaccessible r)
  simpa only [ModelStage.ordinal, Ordinal.rank_toZFSet] using limit

def source (r : Nat) : Ordinal.{u} := D.point (rowEndpoint a r)

theorem source_eq {r e : Nat} {row : Row}
    (hr : rowAt a r = some row) (he : row.e = some e) : D.source r = D.point e := by
  simp only [source, rowEndpoint_eq hr he]

theorem source_bounds {r p : Nat} (hp : predecessor a r = some p) :
    D.point p < D.source r ∧ D.point (p + 1) ≤ D.source r :=
  predecessor_source_bounds D.valid D.shapes D.point_increasing
    (fun _ _ _ hr he => D.source_eq hr he) hp

noncomputable def map (r : FiniteRowIndex a) : stage.BoundedMap (D.source r.val) (D.point (r.val + 1)) :=
  (D.elementary r).toRankEmbedding

theorem graph_represents (r : FiniteRowIndex a) :
    stage.RepresentsBoundedMap (D.graph r) (D.map r) :=
  ModelStage.RepresentsBoundedMap.of_internalGraphElementary (D.elementary r)

theorem predecessor_value (r : FiniteRowIndex a) (p : Nat) (hp : predecessor a r.val = some p) :
    (D.map r (stage.rankOrdinal ⟨D.point p,
      Order.lt_succ_of_le (D.source_bounds hp).1.le⟩)).val = (D.point r.val).toZFSet := by
  obtain ⟨row, hr, pred⟩ := Option.bind_eq_some_iff.mp hp
  have edge := D.edges r row hr (p, r.val)
    (Row.predecessor_edge (D.valid _ _ hr) (D.shapes row (rowAt_mem hr)) pred)
  obtain ⟨x, hx, hy⟩ := (D.graph_represents r).graph_exact _ _ |>.mp edge
  have same : x = stage.rankOrdinal ⟨D.point p,
      Order.lt_succ_of_le (D.source_bounds hp).1.le⟩ := Subtype.ext hx
  simpa only [same] using hy

/-- Both geometric bounds and the p edge are derived from the original row.
There are exactly n saved maps and n+2 saved points. -/
noncomputable def toFiniteTraceRows : FiniteTraceRows stage a D.theta where
  theta_limit := fun i => (D.point_at i) ▸ D.point_limit i.val
  source := fun r => D.source r.val
  source_limit := fun r => D.point_limit (rowEndpoint a r.val)
  map := D.map
  source_gap := fun _ _ hp => (D.source_bounds hp).1
  adjacent_domain := fun _ _ hp => (D.source_bounds hp).2
  predecessor_value := D.predecessor_value

theorem graphs_on_trace {target start : Nat} {rows : List Nat} (h : FactorTrace a target start rows) :
    ∀ r ∈ rows, ∃ graph : stage.model.Element,
      stage.RepresentsBoundedMap graph (D.toFiniteTraceRows.toInternalTraceRows.map r) :=
  D.toFiniteTraceRows.graphs_on_trace (fun r => ⟨D.graph r, D.graph_represents r⟩) h

theorem sources_on_trace {target start : Nat} {rows : List Nat} (h : FactorTrace a target start rows) :
    ∀ r ∈ rows, stage.model.InternalInaccessible
      (stage.ordinal (D.toFiniteTraceRows.toInternalTraceRows.source r)) := by
  intro r hr
  rw [D.toFiniteTraceRows.source_valid ⟨r, h.validRows r hr⟩]
  exact D.point_inaccessible (rowEndpoint a r)

/-- Every accurate trace automatically obtains its actual internal composite
graph, inaccessible natural bound, paired-source edge and endpoint edge. -/
theorem trace_internal_realization {target start : Nat} {rows : List Nat}
    (h : FactorTrace a target start rows) :
    ∃ graph : stage.model.Element,
      stage.InternalGraphElementary
        (h.inputBound D.toFiniteTraceRows.toInternalTraceRows.actions)
        (h.word D.toFiniteTraceRows.toInternalTraceRows.actions).bound graph ∧
      stage.model.InternalInaccessible
        (stage.ordinal (h.word D.toFiniteTraceRows.toInternalTraceRows.actions).bound) ∧
      ZFSet.pair (D.point target).toZFSet (D.point start).toZFSet ∈ graph.val ∧
      ZFSet.pair (h.inputBound D.toFiniteTraceRows.toInternalTraceRows.actions).toZFSet
        (h.word D.toFiniteTraceRows.toInternalTraceRows.actions).bound.toZFSet ∈ graph.val :=
  h.internal_realization D.toFiniteTraceRows.toInternalTraceRows
    (D.graphs_on_trace h) (D.sources_on_trace h)

/-- The stored mark uses its actual paired source, the current algorithmic
trace including its final point, and exactly the word obtained by dropping
that final point. Its weak agreement is required at the computed natural bound. -/
def MarkRealized (r : Nat) (row : Row) (b : Nat) : Prop :=
  ∃ target trace,
    row.columns[row.columns.idxOf b - row.step]? = some target ∧
    markTrace a r b = some trace ∧
    ∃ h : FactorTrace a target b trace.dropLast,
      h.MarkCertificate D.toFiniteTraceRows.toInternalTraceRows r

end FiniteBoundedData

/-- The complete semantic finite realization from section 3. This is a Lean
semantic structure, not yet the single finite object-language Good formula.
Proper marks, accurate traces and their weak certificates are separate genuine
requirements; neither trace existence nor saturation substitutes for (3.14). -/
structure BoundedRealization (stage : ModelStage.{u}) (a : Pattern) where
  data : FiniteBoundedData stage a
  proper : ProperMarks a
  saturated : Saturated a
  marks : ∀ r row b, rowAt a r = some row → b ∈ row.marks → data.MarkRealized r row b

namespace BoundedRealization
variable {stage : ModelStage.{u}} {a : Pattern} (R : BoundedRealization stage a)

def top : Ordinal.{u} := R.data.top

noncomputable def toFiniteTraceRows : FiniteTraceRows stage a R.data.theta :=
  R.data.toFiniteTraceRows

include R in
theorem markTrace_exists {r b : Nat} {row : Row} (hr : rowAt a r = some row)
    (hb : b ∈ row.marks) : ∃ trace, markTrace a r b = some trace := by
  obtain ⟨target, trace, _, computed, _⟩ := R.marks r row b hr hb
  exact ⟨trace, computed⟩

end BoundedRealization
end IBLP
