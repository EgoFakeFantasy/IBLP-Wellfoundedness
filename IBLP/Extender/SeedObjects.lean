import IBLP.Extender.IndexMembership

namespace IBLP.Extender.Ultrapower
open FullMarkedBLP Derivation
universe u
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}
  (D : Derivation stage alpha beta) (ha : Order.IsSuccLimit alpha) (hb : Order.IsSuccLimit beta)

noncomputable def seedObject (a : Seed stage beta) : Ultrapower D ha hb :=
  mk D ha hb ⟨a, identityRepresentative ha⟩

theorem seed_mem_seed (a b : Seed stage beta) :
    Mem D ha hb (seedObject D ha hb a) (seedObject D ha hb b) ↔ a.val ∈ b.val := by
  let family : Fin 2 → SeededRepresentative stage alpha beta :=
    ![⟨a, identityRepresentative ha⟩, ⟨b, identityRepresentative ha⟩]
  let R := CommonRefinement.canonical D ha hb (fun i => (family i).seed)
  change GlobalTruth.Member D ha hb (family 0) (family 1) ↔ _
  rw [GlobalTruth.member_at D ha hb family R 0 1]
  have equivalent : D.Holds R.seed (.member 0 1)
      ![(identityRepresentative ha).pullback (R.maps 0), (identityRepresentative ha).pullback (R.maps 1)] ↔
      D.Holds R.seed (.member 0 1) ![(R.maps 0).toRepresentative, (R.maps 1).toRepresentative] := by
    apply D.holds_congr
    intro x
    change (((identityRepresentative ha).pullback (R.maps 0)).value x).val ∈
      (((identityRepresentative ha).pullback (R.maps 1)).value x).val ↔
      ((R.maps 0).toRepresentative.value x).val ∈ ((R.maps 1).toRepresentative.value x).val
    simp only [Representative.pullback_value, identityRepresentative_value, IndexMap.toRepresentative_value]
  apply equivalent.trans
  rw [D.holds_index_membership, R.projects 0, R.projects 1]
  rfl

/-- A bounded representative is exactly an index graph, so its class is
represented by the projection of the seed and the identity function. -/
theorem bounded_is_seed (seed : Seed stage beta)
    (f : BoundedRepresentative stage alpha (stage.hierarchy alpha)) :
    ∃ a : Seed stage beta, mk D ha hb ⟨seed, f.toRepresentative⟩ = seedObject D ha hb a := by
  let p := IndexMap.ofFunction ha f.graph f.function
  have equivalent : D.RepEquivalent seed f.toRepresentative ((identityRepresentative ha).pullback p) := by
    apply D.holds_of_pointwise
    intro x
    change f.toRepresentative.value x = ((identityRepresentative ha).pullback p).value x
    rw [Representative.pullback_value, identityRepresentative_value]
    exact (bounded_index_value ha f x).symm.trans (p.toRepresentative_value x)
  refine ⟨D.project p seed, ((mk_same_seed_eq_iff D ha hb seed _ _).mpr equivalent).trans ?_⟩
  exact mk_pullback D ha hb seed p (identityRepresentative ha)

/-- All predecessors of an object with pointwise low-rank members are
seed objects; the normalization is an actual function graph in M. -/
theorem predecessor_is_seed (r : SeededRepresentative stage alpha beta)
    (bounded : ∀ x : Seed stage alpha, ∀ y ∈ (r.representative.value x).val,
      y ∈ (stage.hierarchy alpha).val)
    (q : Ultrapower D ha hb) (edge : Mem D ha hb q (mk D ha hb r)) :
    ∃ a : Seed stage beta, q = seedObject D ha hb a := by
  classical
  obtain ⟨s, rfl⟩ := mk_surjective D ha hb q
  let family : Fin 2 → SeededRepresentative stage alpha beta := ![s, r]
  let R := CommonRefinement.canonical D ha hb (fun i => (family i).seed)
  let g := s.representative.pullback (R.maps 0)
  let upper := r.representative.pullback (R.maps 1)
  have large : D.Holds R.seed (.member 0 1) ![g, upper] :=
    (GlobalTruth.member_at D ha hb family R 0 1).mp ((mem_mk D ha hb s r).mp edge)
  have emptyInside : (stage.ordinal 0).val ∈ (stage.hierarchy alpha).val := by
    rw [stage.mem_hierarchy_iff]
    simpa only [ModelStage.ordinal, Ordinal.rank_toZFSet, Nat.cast_zero] using
      (Ordinal.natCast_lt_omega0 0).trans_le (Ordinal.omega0_le_of_isSuccLimit ha)
  obtain ⟨f, preserve⟩ := g.clip_exists (stage.hierarchy alpha) (stage.ordinal 0) emptyInside
  have equivalent : D.RepEquivalent R.seed f.toRepresentative g := by
    apply (D.holds_mono R.seed (.member 0 1) (.equal 0 1) ![g, upper] ![f.toRepresentative, g] ?_) large
    intro x hx
    change (g.value x).val ∈ (upper.value x).val at hx
    change f.toRepresentative.value x = g.value x
    apply preserve x
    change (g.value x).val ∈ ((r.representative.pullback (R.maps 1)).value x).val at hx
    rw [Representative.pullback_value] at hx
    exact bounded (Representative.indexValue (R.maps 1) x) _ hx
  have normalized : mk D ha hb ⟨R.seed, f.toRepresentative⟩ = mk D ha hb s := by
    apply ((mk_same_seed_eq_iff D ha hb _ _ _).mpr equivalent).trans
    change mk D ha hb ⟨R.seed, s.representative.pullback (R.maps 0)⟩ = _
    rw [mk_pullback, R.projects 0]
    rfl
  obtain ⟨a, ha'⟩ := bounded_is_seed D ha hb R.seed f
  exact ⟨a, normalized.symm.trans ha'⟩

theorem predecessor_of_seed (b : Seed stage beta) (q : Ultrapower D ha hb)
    (edge : Mem D ha hb q (seedObject D ha hb b)) :
    ∃ a : Seed stage beta, q = seedObject D ha hb a := by
  apply predecessor_is_seed D ha hb ⟨b, identityRepresentative ha⟩ ?_ q edge
  intro x y hy
  rw [identityRepresentative_value] at hy
  exact stage.hierarchy_transitive alpha x.val ((stage.mem_hierarchy alpha x.val).mpr x.property) hy

end IBLP.Extender.Ultrapower
