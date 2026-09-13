import IBLP.Extender.LocalRelation
import IBLP.Extender.SeedCollapse

namespace IBLP.Extender
open FullMarkedBLP Derivation
universe u
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}
  (D : Derivation stage alpha beta) (ha : Order.IsSuccLimit alpha) (hb : Order.IsSuccLimit beta)
  (inaccessible : stage.model.InternalInaccessible (stage.ordinal beta))

namespace LocalCodes

include hb inaccessible in
theorem wellFounded (bound : stage.model.Element) :
    WellFounded (setRelation (domain stage alpha beta bound).val (relation D ha bound).val) := by
  apply (InvImage.wf (decode D ha hb bound) (Ultrapower.wellFounded D ha hb inaccessible)).mono
  intro c d edge
  exact (relation_iff D ha hb bound c d).mp edge

noncomputable def internalCollapse (bound : stage.model.Element) :
    InternalSetCollapse stage (domain stage alpha beta bound) (relation D ha bound) :=
  stage.setCollapse _ _ (wellFounded D ha hb inaccessible bound)

theorem internalCollapse_agrees (bound fallback : stage.model.Element)
    (transitive : ZFSet.IsTransitive bound.val) (inside : fallback.val ∈ bound.val)
    (c : SetDomain (domain stage alpha beta bound).val) :
    ((internalCollapse D ha hb inaccessible bound).value c).val =
      Ultrapower.collapsedValue D ha hb inaccessible (decode D ha hb bound c) := by
  induction c using (wellFounded D ha hb inaccessible bound).induction with
  | h c ih =>
    apply ZFSet.ext
    intro z
    rw [InternalSetCollapse.mem_value, Ultrapower.mem_collapsedValue]
    constructor
    · rintro ⟨d, edge, same⟩
      exact ⟨decode D ha hb bound d, (relation_iff D ha hb bound d c).mp edge,
        (ih d edge).symm.trans same⟩
    · rintro ⟨q, edge, same⟩
      obtain ⟨d, hd⟩ := predecessor_closed D ha hb bound fallback transitive inside c q edge
      have localEdge := (relation_iff D ha hb bound d c).mpr (hd.symm ▸ edge)
      refine ⟨d, localEdge, (ih d localEdge).trans ?_⟩
      rw [hd]
      exact same

end LocalCodes

namespace Ultrapower

theorem collapsedValue_internal (q : Ultrapower D ha hb) :
    collapsedValue D ha hb inaccessible q ∈ stage.model.carrier := by
  obtain ⟨bound, fallback, transitive, inside, c, hc⟩ := LocalCodes.covers D ha hb q
  have agreement := LocalCodes.internalCollapse_agrees D ha hb inaccessible bound fallback transitive inside c
  rw [hc] at agreement
  exact agreement ▸ ((LocalCodes.internalCollapse D ha hb inaccessible bound).value c).property

/-- The entire transitive collapse is contained in the original model.
The proof uses actual internal code sets, relations, and recursive graphs. -/
theorem target_subset : (target D ha hb inaccessible).carrier ⊆ stage.model.carrier := by
  rintro x ⟨q, rfl⟩
  exact collapsedValue_internal D ha hb inaccessible q

end Ultrapower
end IBLP.Extender
