import IBLP.Extender.CollapsedLos
import IBLP.Extender.SequenceRepresentative
import IBLP.Model.SequenceGraphExact

namespace IBLP.Extender.Ultrapower
open FullMarkedBLP Derivation
universe u
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}
  (D : Derivation stage alpha beta) (ha : Order.IsSuccLimit alpha) (hb : Order.IsSuccLimit beta)
  (inaccessible : stage.model.InternalInaccessible (stage.ordinal beta))

/-- Complete external countable closure of the constructed target, for
arbitrary target elements and their full sequence graph. -/
theorem countablyClosed : (target D ha hb inaccessible).CountablyClosed := by
  classical
  let N := target D ha hb inaccessible
  intro ys
  choose qs hqs using fun n => (collapseMap_bijective D ha hb inaccessible).2 (ys n)
  choose rs hrs using fun n => mk_surjective D ha hb (qs n)
  obtain ⟨common, projections, projectEq⟩ := D.countable_directed ha inaccessible (fun n => (rs n).seed)
  let fs : Nat → Representative stage alpha := fun n => (rs n).representative.pullback (projections n)
  have valueEq (n : Nat) : collapseComponent D ha hb inaccessible common (fs n) = ys n := by
    change collapseMap D ha hb inaccessible (mk D ha hb ⟨common, (rs n).representative.pullback (projections n)⟩) = _
    rw [mk_pullback, projectEq, hrs]
    exact hqs n
  obtain ⟨h, hspec⟩ := Representative.sequence_exists fs
  let H := collapseComponent D ha hb inaccessible common h
  let omega : Representative stage alpha := Representative.constant (stage.ordinal Ordinal.omega0)
  have hlarge : D.Holds common functionDomainMatrix ![h, omega] := by
    apply D.holds_of_pointwise
    intro x
    have args : (fun i : Fin 2 => (![h, omega] i).value x) = ![h.value x, stage.ordinal Ordinal.omega0] := by
      funext i; fin_cases i
      · rfl
      · exact Representative.constant_value _ _
    rw [args, functionDomainMatrix_realize]
    exact (hspec x).1
  have functional := (realize_component D ha hb inaccessible functionDomainMatrix common ![h, omega]).mpr hlarge
  have args : (fun i : Fin 2 => collapseComponent D ha hb inaccessible common (![h, omega] i)) =
      ![H, embedding D ha hb inaccessible (stage.ordinal Ordinal.omega0)] := by
    funext i; fin_cases i
    · rfl
    · exact collapseComponent_constant D ha hb inaccessible common _
  rw [args, functionDomainMatrix_realize] at functional
  obtain ⟨range, function⟩ := functional
  rw [stage.ordinal_omega_image_val] at function
  have edges (n : Nat) : ZFSet.pair (n : Ordinal.{u}).toZFSet (ys n).val ∈ H.val := by
    let natural : Representative stage alpha := Representative.constant (stage.ordinal (n : Ordinal.{u}))
    let phi : RankPredicateFormula 0 3 := rankFormulaGraphApplies 0 1 2
    have large : D.Holds common phi ![h, natural, fs n] := by
      apply D.holds_of_pointwise
      intro x
      rw [stage.model.setGraphAtom_realize]
      change ZFSet.pair ((natural.value x).val) (((fs n).value x).val) ∈ (h.value x).val
      rw [Representative.constant_value]
      exact (hspec x).2 n
    have image := (realize_component D ha hb inaccessible phi common ![h, natural, fs n]).mpr large
    rw [N.setGraphAtom_realize] at image
    change ZFSet.pair (collapseComponent D ha hb inaccessible common natural).val
      (collapseComponent D ha hb inaccessible common (fs n)).val ∈ H.val at image
    rw [collapseComponent_constant, stage.ordinal_nat_image_val, valueEq] at image
    exact image
  have same := N.sequenceGraph_eq_of_function ys function edges
  rw [← same]
  exact H.property

/-- The extender construction is now a genuine next model stage. -/
noncomputable def nextStage : ModelStage.{u} :=
  stage.next (target D ha hb inaccessible) (embedding D ha hb inaccessible) (countablyClosed D ha hb inaccessible)

end IBLP.Extender.Ultrapower
