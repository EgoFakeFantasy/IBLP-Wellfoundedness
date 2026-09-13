import IBLP.Model.SetSatisfaction
import FullMarkedBLP.FunctionGraphConstruction

namespace IBLP
open FullMarkedBLP
universe u

theorem setAssignment_function {D : ZFSet.{u}} {n : Nat} (values : Fin n → SetDomain D) :
    ZFSet.IsFunc (n : Ordinal.{u}).toZFSet D (setAssignment values) := by
  constructor
  · intro p hp
    obtain ⟨i, rfl⟩ := (mem_setAssignment _ _).mp hp
    exact ZFSet.pair_mem_prod.mpr ⟨(finZFSetEquiv n i).property, (values i).property⟩
  · intro a ha
    let i := (finZFSetEquiv n).symm ⟨a, ha⟩
    have hi : a = (i.val : Ordinal.{u}).toZFSet :=
      (congrArg Subtype.val ((finZFSetEquiv n).apply_symm_apply ⟨a, ha⟩)).symm
    refine ⟨(values i).val, (setAssignment_applies_iff _ _ _).mpr ⟨i, hi, rfl⟩, ?_⟩
    intro b hb
    obtain ⟨j, hj, he⟩ := (setAssignment_applies_iff _ _ _).mp hb
    have hij : i = j := Fin.ext (Nat.cast_injective (Ordinal.toZFSet_injective (hi.symm.trans hj)))
    simpa only [hij] using he

theorem setAssignment_decode {D graph : ZFSet.{u}} {n : Nat}
    (h : ZFSet.IsFunc (n : Ordinal.{u}).toZFSet D graph) :
    ∃ values : Fin n → SetDomain D, setAssignment values = graph := by
  let f := zfGraphFunction h
  let values : Fin n → SetDomain D := fun i => f (finZFSetEquiv n i)
  refine ⟨values, ?_⟩
  apply ZFSet.ext
  intro p
  constructor
  · intro hp
    obtain ⟨i, rfl⟩ := (mem_setAssignment _ _).mp hp
    have hf := zfGraphFunction_edge h (finZFSetEquiv n i)
    exact hf
  · intro hp
    obtain ⟨a, ha, b, hb, rfl⟩ := ZFSet.mem_prod.mp (h.1 hp)
    let i := (finZFSetEquiv n).symm ⟨a, ha⟩
    have hi : a = (i.val : Ordinal.{u}).toZFSet :=
      (congrArg Subtype.val ((finZFSetEquiv n).apply_symm_apply ⟨a, ha⟩)).symm
    have hb' : b = (values i).val := by
      have app := zfGraphFunction_edge h ⟨a, ha⟩
      have unique := (h.2 a ha).choose_spec.2
      have same := (unique b hp).trans ((unique (zfGraphFunction h ⟨a, ha⟩).val app).symm)
      simpa only [values, i, Equiv.apply_symm_apply] using same
    exact (setAssignment_applies_iff _ _ _).mpr ⟨i, hi, hb'⟩

theorem setAssignment_applies_nat_iff {D : ZFSet.{u}} {n : Nat}
    (values : Fin n → SetDomain D) (i : Fin n) (b : ZFSet.{u}) :
    ZFSet.pair (i.val : Ordinal.{u}).toZFSet b ∈ setAssignment values ↔ b = (values i).val := by
  rw [setAssignment_applies_iff]
  constructor
  · rintro ⟨j, hj, hb⟩
    have hi : i = j := Fin.ext (Nat.cast_injective (Ordinal.toZFSet_injective hj))
    simpa only [hi] using hb
  · exact fun hb => ⟨i, rfl, hb⟩

end IBLP

