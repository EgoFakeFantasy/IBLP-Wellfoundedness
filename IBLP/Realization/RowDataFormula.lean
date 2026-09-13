import IBLP.Model.RankGraphFormula
import IBLP.Model.UniformGraphOperations
import IBLP.Encoding.RealizationCode

namespace IBLP
open FullMarkedBLP
universe u

def finitePointIndex (a : Pattern) (r : Nat) : Fin (a.length + 2) :=
  ⟨min r (a.length + 1), by omega⟩

/-- A finite, purely relational presentation of all the unmarked row data.
The points and graph sets are the only variable data. -/
structure RowDataPayload (stage : ModelStage.{u}) (a : Pattern)
    (points : Fin (a.length + 2) → stage.model.Element)
    (graphs : FiniteRowIndex a → stage.model.Element) : Prop where
  ordinals : ∀ i, ZFSet.IsOrdinal (points i).val
  increasing : ∀ i j, i < j → (points i).val ∈ (points j).val
  inaccessible : ∀ i, stage.model.InternalInaccessible (points i)
  valid : BasicValid a
  shapes : OrdinaryShape a
  elementary : ∀ r : FiniteRowIndex a, ∃ alpha beta : Ordinal.{u},
    points (finitePointIndex a (rowEndpoint a r.val)) = stage.ordinal alpha ∧
    points (finitePointIndex a (r.val + 1)) = stage.ordinal beta ∧
    stage.InternalGraphElementary alpha beta (graphs r)
  critical : ∀ r row minimum, rowAt a r.val = some row → row.columns.head? = some minimum →
    stage.model.GraphCriticalPoint (graphs r) (points (finitePointIndex a minimum))
  edges : ∀ r row, rowAt a r.val = some row → ∀ edge ∈ row.edgePairs r.val,
    ZFSet.pair (points (finitePointIndex a edge.1)).val
      (points (finitePointIndex a edge.2)).val ∈ (graphs r).val

theorem UniformDefinable.row_data (a : Pattern) {n : Nat}
    (points : Fin (a.length + 2) → Fin n) (graphs : FiniteRowIndex a → Fin n) :
    UniformDefinable (fun (stage : ModelStage.{u}) v =>
      RowDataPayload stage a (v ∘ points) (v ∘ graphs)) := by
  classical
  letI : Fintype (FiniteRowIndex a) := Fintype.ofEquiv (Fin a.length) (finiteRowEquiv a)
  have ords := finite_all _ (fun i => ordinal.relabel ![points i])
  have increasing := finite_all _ (fun i => finite_all _ (fun j =>
    (constant (i < j)).imp (member (points i) (points j))))
  have inaccess := finite_all _ (fun i => inaccessible.relabel ![points i])
  have elementary := finite_all _ (fun r => rank_graph.relabel
    ![points (finitePointIndex a (rowEndpoint a r.val)), points (finitePointIndex a (r.val + 1)), graphs r])
  have critical := finite_all _ (fun r : FiniteRowIndex a =>
    list_all (rowAt a r.val).toList _ (fun row _ =>
      list_all row.columns.head?.toList _ (fun minimum _ =>
        graph_critical.relabel ![graphs r, points (finitePointIndex a minimum)])))
  have edges := finite_all _ (fun r : FiniteRowIndex a =>
    list_all (rowAt a r.val).toList _ (fun row _ =>
      list_all (row.edgePairs r.val) _ (fun edge _ =>
        graph_edge.relabel ![graphs r, points (finitePointIndex a edge.1), points (finitePointIndex a edge.2)])))
  refine (ords.and (increasing.and (inaccess.and ((constant (BasicValid a)).and
    ((constant (OrdinaryShape a)).and (elementary.and (critical.and edges))))))).congr ?_
  intro stage v
  simp only [Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_succ, Option.mem_toList]
  constructor
  · rintro ⟨ho, hi, hk, hv, hs, he, hc, hh⟩
    exact ⟨ho, hi, hk, hv, hs, he, fun r row minimum hr hm => hc r row hr minimum hm, hh⟩
  · intro h
    exact ⟨h.ordinals, h.increasing, h.inaccessible, h.valid, h.shapes, h.elementary,
      fun r row hr minimum hm => h.critical r row minimum hr hm, h.edges⟩

namespace RowDataPayload
variable {stage : ModelStage.{u}} {a : Pattern}
  {points : Fin (a.length + 2) → stage.model.Element}
  {graphs : FiniteRowIndex a → stage.model.Element} (h : RowDataPayload stage a points graphs)

include h in
theorem point_eq (i : Fin (a.length + 2)) : points i = stage.ordinal (points i).val.rank :=
  Subtype.ext (h.ordinals i).toZFSet_rank_eq.symm

/-- Decode exactly the original semantic structure; no point, graph,
critical-point or edge clause is discarded. -/
noncomputable def decode : FiniteBoundedData stage a where
  theta := fun i => (points i).val.rank
  increasing := by
    intro i j smaller
    have member := h.increasing i j smaller
    rw [h.point_eq i, h.point_eq j] at member
    exact Ordinal.toZFSet_mem_toZFSet_iff.mp member
  inaccessible := fun i => h.point_eq i ▸ h.inaccessible i
  valid := h.valid
  shapes := h.shapes
  graph := graphs
  elementary := by
    intro r
    obtain ⟨alpha, beta, ha, hb, elementary⟩ := h.elementary r
    have sa : alpha = (points (finitePointIndex a (rowEndpoint a r.val))).val.rank := by
      simpa only [ModelStage.ordinal, Ordinal.rank_toZFSet] using (congrArg (fun x => x.val.rank) ha).symm
    have sb : beta = (points (finitePointIndex a (r.val + 1))).val.rank := by
      simpa only [ModelStage.ordinal, Ordinal.rank_toZFSet] using (congrArg (fun x => x.val.rank) hb).symm
    rw [sa, sb] at elementary
    exact elementary
  critical := by
    intro r row minimum hr hm
    exact h.point_eq (finitePointIndex a minimum) ▸ h.critical r row minimum hr hm
  edges := by
    intro r row hr edge member
    have he := h.edges r row hr edge member
    rw [h.point_eq (finitePointIndex a edge.1), h.point_eq (finitePointIndex a edge.2)] at he
    exact he

theorem decode_points (i : Fin (a.length + 2)) :
    stage.ordinal (h.decode.theta i) = points i := (h.point_eq i).symm

theorem decode_graphs (r : FiniteRowIndex a) : h.decode.graph r = graphs r := rfl

end RowDataPayload

theorem FiniteBoundedData.rowDataPayload {stage : ModelStage.{u}} {a : Pattern}
    (D : FiniteBoundedData stage a) :
    RowDataPayload stage a (fun i => stage.ordinal (D.theta i)) D.graph where
  ordinals := fun i => ZFSet.isOrdinal_toZFSet _
  increasing := fun i j smaller => Ordinal.toZFSet_mem_toZFSet_iff.mpr (D.increasing smaller)
  inaccessible := D.inaccessible
  valid := D.valid
  shapes := D.shapes
  elementary := fun r => ⟨_, _, rfl, rfl, D.elementary r⟩
  critical := D.critical
  edges := D.edges

end IBLP
