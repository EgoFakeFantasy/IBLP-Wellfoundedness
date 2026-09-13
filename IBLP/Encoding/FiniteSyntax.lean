import IBLP.Syntax
import IBLP.Model.FiniteGraph
import FullMarkedBLP.RankOrderedPair

namespace IBLP
open FullMarkedBLP
universe u

/-- Ordered finite lists are nested Kuratowski pairs terminated by the empty
set. Their length is part of the code; no padding or normalization is used. -/
noncomputable def listSetCode : List ZFSet.{u} → ZFSet.{u}
  | [] => ∅
  | x :: xs => ZFSet.pair x (listSetCode xs)

theorem orderedPair_ne_empty (x y : ZFSet.{u}) : ZFSet.pair x y ≠ ∅ := by
  intro h
  have mem : ({x, x} : ZFSet.{u}) ∈ ZFSet.pair x y := by simp [ZFSet.pair]
  rw [h] at mem
  simp at mem

theorem listSetCode_injective : Function.Injective (listSetCode : List ZFSet.{u} → ZFSet.{u}) := by
  intro xs
  induction xs with
  | nil =>
    intro ys eq
    cases ys with
    | nil => rfl
    | cons y ys => exact False.elim (orderedPair_ne_empty y (listSetCode ys) eq.symm)
  | cons x xs ih =>
    intro ys eq
    cases ys with
    | nil => exact False.elim (orderedPair_ne_empty x (listSetCode xs) eq)
    | cons y ys =>
      obtain ⟨head, tail⟩ := ZFSet.pair_inj.mp eq
      exact congrArg₂ List.cons head (ih tail)

theorem listSetCode_rank_lt {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (xs : List ZFSet.{u}) (small : ∀ x ∈ xs, x.rank < lambda) :
    (listSetCode xs).rank < lambda := by
  induction xs with
  | nil => simpa only [listSetCode, ZFSet.rank_empty] using hl.pos
  | cons x xs ih =>
    exact rank_orderedPair_lt_of_limit hl (small x (List.mem_cons_self ..))
      (ih (fun y hy => small y (List.mem_cons_of_mem x hy)))

noncomputable def natListSetCode (xs : List Nat) : ZFSet.{u} :=
  listSetCode (xs.map (fun n : Nat => (n : Ordinal.{u}).toZFSet))

theorem natListSetCode_injective : Function.Injective (natListSetCode : List Nat → ZFSet.{u}) := by
  intro xs ys eq
  apply List.map_injective_iff.mpr (fun _ _ h => Nat.cast_injective (Ordinal.toZFSet_injective h))
  exact listSetCode_injective eq

theorem natListSetCode_rank_lt_omega (xs : List Nat) :
    (natListSetCode xs : ZFSet.{u}).rank < Ordinal.omega0 := by
  apply listSetCode_rank_lt Ordinal.isSuccLimit_omega0
  intro z hz
  obtain ⟨n, _, rfl⟩ := List.mem_map.mp hz
  simpa only [Ordinal.rank_toZFSet] using Ordinal.natCast_lt_omega0 n

/-- Every column, step and mark is retained, including its original order. -/
noncomputable def Row.setCode (row : Row) : ZFSet.{u} :=
  ZFSet.pair (natListSetCode row.columns)
    (ZFSet.pair (row.step : Ordinal.{u}).toZFSet (natListSetCode row.marks))

theorem Row.setCode_injective : Function.Injective (Row.setCode : Row → ZFSet.{u}) := by
  intro x y h
  obtain ⟨columns, rest⟩ := ZFSet.pair_inj.mp h
  obtain ⟨step, marks⟩ := ZFSet.pair_inj.mp rest
  have hc := natListSetCode_injective columns
  have hs : x.step = y.step := Nat.cast_injective (Ordinal.toZFSet_injective step)
  have hm := natListSetCode_injective marks
  cases x
  cases y
  simp_all

theorem Row.setCode_rank_lt_omega (row : Row) :
    (row.setCode : ZFSet.{u}).rank < Ordinal.omega0 := by
  apply rank_orderedPair_lt_of_limit Ordinal.isSuccLimit_omega0
  · exact natListSetCode_rank_lt_omega row.columns
  · apply rank_orderedPair_lt_of_limit Ordinal.isSuccLimit_omega0
    · simpa only [Ordinal.rank_toZFSet] using Ordinal.natCast_lt_omega0 row.step
    · exact natListSetCode_rank_lt_omega row.marks

noncomputable def patternSetCode (a : Pattern) : ZFSet.{u} := listSetCode (a.map Row.setCode)

theorem patternSetCode_injective : Function.Injective (patternSetCode : Pattern → ZFSet.{u}) := by
  intro a b eq
  exact List.map_injective_iff.mpr Row.setCode_injective (listSetCode_injective eq)

theorem patternSetCode_rank_lt_omega (a : Pattern) :
    (patternSetCode a : ZFSet.{u}).rank < Ordinal.omega0 := by
  apply listSetCode_rank_lt Ordinal.isSuccLimit_omega0
  intro z hz
  obtain ⟨row, _, rfl⟩ := List.mem_map.mp hz
  exact row.setCode_rank_lt_omega

noncomputable def ModelStage.listCode (stage : ModelStage.{u}) :
    List stage.model.Element → stage.model.Element
  | [] => stage.ordinal 0
  | x :: xs => stage.orderedPair x (stage.listCode xs)

theorem ModelStage.listCode_val (stage : ModelStage.{u}) (xs : List stage.model.Element) :
    (stage.listCode xs).val = listSetCode (xs.map Subtype.val) := by
  induction xs with
  | nil => change (0 : Ordinal.{u}).toZFSet = ∅; simp
  | cons x xs ih => simp [listCode, stage.orderedPair_val, List.map, listSetCode, ih]

noncomputable def ModelStage.natListCode (stage : ModelStage.{u}) (xs : List Nat) : stage.model.Element :=
  stage.listCode (xs.map (fun n : Nat => stage.ordinal (n : Ordinal.{u})))

theorem ModelStage.natListCode_val (stage : ModelStage.{u}) (xs : List Nat) :
    (stage.natListCode xs).val = natListSetCode xs := by
  rw [natListCode, stage.listCode_val]
  change listSetCode (List.map Subtype.val (List.map (fun n : Nat => stage.ordinal (n : Ordinal.{u})) xs)) = _
  rw [List.map_map]
  rfl

noncomputable def ModelStage.rowCode (stage : ModelStage.{u}) (row : Row) : stage.model.Element :=
  stage.orderedPair (stage.natListCode row.columns)
    (stage.orderedPair (stage.ordinal row.step) (stage.natListCode row.marks))

theorem ModelStage.rowCode_val (stage : ModelStage.{u}) (row : Row) :
    (stage.rowCode row).val = row.setCode := by
  simp only [rowCode, stage.orderedPair_val, stage.natListCode_val, ordinal, Row.setCode]

noncomputable def ModelStage.patternCode (stage : ModelStage.{u}) (a : Pattern) : stage.model.Element :=
  stage.listCode (a.map stage.rowCode)

theorem ModelStage.patternCode_val (stage : ModelStage.{u}) (a : Pattern) :
    (stage.patternCode a).val = patternSetCode a := by
  rw [patternCode, stage.listCode_val]
  change listSetCode (List.map Subtype.val (List.map stage.rowCode a)) = _
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro row _
  exact stage.rowCode_val row

theorem ModelStage.patternCode_injective (stage : ModelStage.{u}) :
    Function.Injective stage.patternCode := by
  intro a b eq
  apply patternSetCode_injective
  simpa only [stage.patternCode_val] using congrArg Subtype.val eq

end IBLP
