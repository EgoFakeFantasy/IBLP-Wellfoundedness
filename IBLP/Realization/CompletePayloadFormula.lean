import IBLP.Realization.MarkPayloadFormula

namespace IBLP
open FullMarkedBLP
universe u

/-- A harmless default extends the saved row vector; every genuine trace
uses only the actual, positive row indices. -/
def extendRowVector {α : Type*} (a : Pattern) (fallback : α) (graphs : FiniteRowIndex a → α) (r : Nat) : α :=
  if valid : 0 < r ∧ r ≤ a.length then graphs ⟨r, valid⟩ else fallback

theorem extendRowVector_valid {α : Type*} (a : Pattern) (fallback : α)
    (graphs : FiniteRowIndex a → α) (r : FiniteRowIndex a) :
    extendRowVector a fallback graphs r.val = graphs r := dif_pos r.property

theorem extendRowVector_comp {α β : Type*} (a : Pattern) (f : α → β) (fallback : α)
    (graphs : FiniteRowIndex a → α) :
    f ∘ extendRowVector a fallback graphs = extendRowVector a (f fallback) (f ∘ graphs) := by
  funext r
  by_cases valid : 0 < r ∧ r ≤ a.length <;> simp [extendRowVector, valid, Function.comp_def]

def CompletePayload (stage : ModelStage.{u}) (a : Pattern)
    (points : Fin (a.length + 2) → stage.model.Element) (graphs : FiniteRowIndex a → stage.model.Element) : Prop :=
  RowDataPayload stage a points graphs ∧ ProperMarks a ∧ Saturated a ∧
    ∀ r : FiniteRowIndex a, ∀ row ∈ (rowAt a r.val).toList, ∀ b ∈ row.marks,
      MarkPayload stage a points (extendRowVector a (points 0) graphs) r.val row b

theorem UniformDefinable.complete_payload (a : Pattern) {n : Nat}
    (points : Fin (a.length + 2) → Fin n) (graphs : FiniteRowIndex a → Fin n) :
    UniformDefinable (fun (stage : ModelStage.{u}) v => CompletePayload stage a (v ∘ points) (v ∘ graphs)) := by
  classical
  letI : Fintype (FiniteRowIndex a) := Fintype.ofEquiv (Fin a.length) (finiteRowEquiv a)
  have marks := finite_all _ (fun r : FiniteRowIndex a =>
    list_all (rowAt a r.val).toList _ (fun row _ =>
      list_all row.marks _ (fun b _ => mark_payload a points
        (extendRowVector a (points 0) graphs) r.val row b)))
  exact ((row_data a points graphs).and ((constant (ProperMarks a)).and
    ((constant (Saturated a)).and marks))).congr (fun stage v => by
      unfold CompletePayload
      rw [extendRowVector_comp]
      rfl)

namespace CompletePayload
variable {stage : ModelStage.{u}} {a : Pattern}
  {points : Fin (a.length + 2) → stage.model.Element} {graphs : FiniteRowIndex a → stage.model.Element}
  (h : CompletePayload stage a points graphs)

/-- Decode the entire manuscript realization, retaining saturation and
the accurate trace and weak certificate for every original mark. -/
noncomputable def decode : BoundedRealization stage a where
  data := h.1.decode
  proper := h.2.1
  saturated := h.2.2.1
  marks := by
    intro r row b hr hb
    let index : FiniteRowIndex a := ⟨r, rowAt_pos hr, rowAt_le_length hr⟩
    have mark := h.2.2.2 index row (Option.mem_toList.mpr hr) b hb
    have pointsEq : (fun i => stage.ordinal (h.1.decode.theta i)) = points :=
      funext h.1.decode_points
    apply (h.1.decode.markPayload_iff index row b (extendRowVector a (points 0) graphs)
      (fun i => extendRowVector_valid a _ graphs i)).mp
    rwa [pointsEq]

theorem decode_points (i : Fin (a.length + 2)) : stage.ordinal (h.decode.data.theta i) = points i :=
  h.1.decode_points i

theorem decode_graphs (r : FiniteRowIndex a) : h.decode.data.graph r = graphs r := rfl

end CompletePayload

theorem BoundedRealization.completePayload {stage : ModelStage.{u}} {a : Pattern}
    (R : BoundedRealization stage a) :
    CompletePayload stage a (fun i => stage.ordinal (R.data.theta i)) R.data.graph := by
  refine ⟨R.data.rowDataPayload, R.proper, R.saturated, ?_⟩
  intro r row member b hb
  exact (R.data.markPayload_iff r row b _ (fun i => extendRowVector_valid a _ R.data.graph i)).mpr
    (R.marks r.val row b (Option.mem_toList.mp member) hb)

end IBLP
