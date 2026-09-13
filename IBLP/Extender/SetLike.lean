import IBLP.Extender.BoundedRepresentative
import IBLP.Extender.GlobalEmbedding

namespace IBLP.Extender
open FullMarkedBLP Derivation
universe u
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}

instance seedSmall : Small.{u} (Seed stage beta) := by
  let code : Seed stage beta → (stage.hierarchy beta).val :=
    fun s => ⟨s.val, (stage.mem_hierarchy beta s.val).mpr s.property⟩
  apply small_of_injective (f := code)
  intro s t h
  apply Subtype.ext
  exact congrArg (fun z : (stage.hierarchy beta).val => z.val) h

namespace Ultrapower
variable (D : Derivation stage alpha beta) (ha : Order.IsSuccLimit alpha) (hb : Order.IsSuccLimit beta)

theorem mk_pullback (seed : Seed stage beta) (p : IndexMap stage alpha) (f : Representative stage alpha) :
    mk D ha hb ⟨seed, f.pullback p⟩ = mk D ha hb ⟨D.project p seed, f⟩ :=
  ofComponent_transition D ha hb seed p (UltrapowerAt.mk D (D.project p seed) f)

noncomputable def predecessorBound (r : SeededRepresentative stage alpha beta) : stage.model.Element :=
  stage.hierarchy (Order.succ r.representative.range.val.rank)

/-- Every predecessor has a representative whose values lie in one set
depending only on the given upper object. The modification is internal. -/
theorem bounded_predecessor (r : SeededRepresentative stage alpha beta)
    (q : Ultrapower D ha hb) (edge : Mem D ha hb q (mk D ha hb r)) :
    ∃ seed : Seed stage beta, ∃ f : BoundedRepresentative stage alpha (predecessorBound r),
      mk D ha hb ⟨seed, f.toRepresentative⟩ = q := by
  classical
  obtain ⟨s, rfl⟩ := mk_surjective D ha hb q
  let family : Fin 2 → SeededRepresentative stage alpha beta := ![s, r]
  let R := CommonRefinement.canonical D ha hb (fun i => (family i).seed)
  let g := s.representative.pullback (R.maps 0)
  let upper := r.representative.pullback (R.maps 1)
  have large : D.Holds R.seed (.member 0 1) ![g, upper] :=
    (GlobalTruth.member_at D ha hb family R 0 1).mp ((mem_mk D ha hb s r).mp edge)
  have emptyInside : (stage.ordinal 0).val ∈ (predecessorBound r).val := by
    rw [predecessorBound, stage.mem_hierarchy_iff]
    simp only [ModelStage.ordinal, Ordinal.rank_toZFSet]
    exact Order.lt_succ_of_le zero_le
  obtain ⟨f, preserve⟩ := g.clip_exists (predecessorBound r) (stage.ordinal 0) emptyInside
  have equivalent : D.RepEquivalent R.seed f.toRepresentative g := by
    apply (D.holds_mono R.seed (.member 0 1) (.equal 0 1) ![g, upper] ![f.toRepresentative, g] ?_) large
    intro x hx
    change (g.value x).val ∈ (upper.value x).val at hx
    change f.toRepresentative.value x = g.value x
    apply preserve x
    apply (stage.mem_hierarchy_iff _ _).mpr
    have bounded : (upper.value x).val ∈ r.representative.range.val := upper.value_mem x
    exact (ZFSet.rank_lt_of_mem hx).trans
      ((ZFSet.rank_lt_of_mem bounded).trans (Order.lt_succ _))
  refine ⟨R.seed, f, ((mk_same_seed_eq_iff D ha hb _ _ _).mpr equivalent).trans ?_⟩
  change mk D ha hb ⟨R.seed, s.representative.pullback (R.maps 0)⟩ = _
  rw [mk_pullback, R.projects 0]
  rfl

/-- Set-likeness at the original universe level, despite the proper-class
collection of unrestricted internal representative graphs. -/
instance predecessorsSmall (q : Ultrapower D ha hb) : Small.{u} {p // Mem D ha hb p q} := by
  classical
  obtain ⟨r, rfl⟩ := mk_surjective D ha hb q
  let Code := Seed stage beta × BoundedRepresentative stage alpha (predecessorBound r)
  let decode : Code → Ultrapower D ha hb := fun c => mk D ha hb ⟨c.1, c.2.toRepresentative⟩
  apply small_of_injective_of_exists decode (g := Subtype.val) Subtype.val_injective
  intro p
  obtain ⟨seed, f, h⟩ := bounded_predecessor D ha hb r p.val p.property
  exact ⟨⟨seed, f⟩, h⟩

end Ultrapower
end IBLP.Extender
