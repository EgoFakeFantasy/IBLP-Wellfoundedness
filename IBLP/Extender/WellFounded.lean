import IBLP.Extender.CountableTests
import IBLP.Extender.GlobalExtensionality
import Mathlib.Order.WellFounded

namespace IBLP.Extender
open FullMarkedBLP Derivation
universe u
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}

theorem Derivation.no_descending_representatives (D : Derivation stage alpha beta)
    (ha : Order.IsSuccLimit alpha) (hb : Order.IsSuccLimit beta)
    (seed : Seed stage beta) (fs : Nat → Representative stage alpha)
    (descending : ∀ n, D.Holds seed (.member 0 1) ![fs (n + 1), fs n]) : False := by
  obtain ⟨x, hx⟩ := D.countable_complete ha hb seed
    (fun n => formulaTest (.member 0 1) ![fs (n + 1), fs n]) descending
  have edges (n : Nat) : ((fs (n + 1)).value x).val ∈ ((fs n).value x).val :=
    (mem_formulaTest (.member 0 1) ![fs (n + 1), fs n] x).mp (hx n)
  exact (wellFounded_iff_isEmpty_descending_chain.mp ZFSet.mem_wf).false
    ⟨fun n => ((fs n).value x).val, edges⟩

namespace Ultrapower
variable (D : Derivation stage alpha beta) (ha : Order.IsSuccLimit alpha) (hb : Order.IsSuccLimit beta)

/-- An arbitrary external countable descent can be represented at one
actual countable seed. Countable completeness then produces a descent
in the ambient set universe, contradicting Foundation. -/
theorem no_descending_chain
    (inaccessible : stage.model.InternalInaccessible (stage.ordinal beta))
    (q : Nat → Ultrapower D ha hb) (descending : ∀ n, Mem D ha hb (q (n + 1)) (q n)) : False := by
  classical
  choose rs hrs using fun n => mk_surjective D ha hb (q n)
  obtain ⟨common, projections, project_eq⟩ :=
    D.countable_directed ha inaccessible (fun n => (rs n).seed)
  let fs : Nat → Representative stage alpha := fun n => (rs n).representative.pullback (projections n)
  apply D.no_descending_representatives ha hb common fs
  intro n
  let family : Fin 2 → SeededRepresentative stage alpha beta := ![rs (n + 1), rs n]
  let R : CommonRefinement D (fun i => (family i).seed) :=
    { seed := common
      maps := ![projections (n + 1), projections n]
      projects := by intro i; fin_cases i <;> exact project_eq _ }
  have h : GlobalTruth.Member D ha hb (rs (n + 1)) (rs n) := by
    apply (mem_mk D ha hb _ _).mp
    rw [hrs, hrs]
    exact descending n
  exact (GlobalTruth.member_at D ha hb family R 0 1).mp h

/-- External well-foundedness of the actual global extender quotient.
No well-foundedness or collapse certificate is assumed. -/
theorem wellFounded
    (inaccessible : stage.model.InternalInaccessible (stage.ordinal beta)) :
    WellFounded (Mem D ha hb) :=
  wellFounded_iff_isEmpty_descending_chain.mpr
    ⟨fun ⟨q, hq⟩ => no_descending_chain D ha hb inaccessible q hq⟩

end Ultrapower
end IBLP.Extender
