import IBLP.Extender.LocalCodes

namespace IBLP.Extender.LocalCodes
open FullMarkedBLP Derivation Ultrapower
universe u
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}
  (D : Derivation stage alpha beta) (ha : Order.IsSuccLimit alpha) (hb : Order.IsSuccLimit beta)

noncomputable def decode (bound : stage.model.Element) (c : SetDomain (domain stage alpha beta bound).val) :
    Ultrapower D ha hb := mk D ha hb (representative bound c)

theorem decode_encode (bound : stage.model.Element) (c : Seed stage beta × BoundedRepresentative stage alpha bound) :
    decode D ha hb bound (encode bound c) = mk D ha hb ⟨c.1, c.2.toRepresentative⟩ := by
  rw [decode, representative_encode]

theorem predecessor_closed (bound fallback : stage.model.Element) (transitive : ZFSet.IsTransitive bound.val)
    (inside : fallback.val ∈ bound.val) (c : SetDomain (domain stage alpha beta bound).val)
    (q : Ultrapower D ha hb) (edge : Mem D ha hb q (decode D ha hb bound c)) :
    ∃ d : SetDomain (domain stage alpha beta bound).val, decode D ha hb bound d = q := by
  classical
  obtain ⟨s, rfl⟩ := mk_surjective D ha hb q
  let r := representative bound c
  let family : Fin 2 → SeededRepresentative stage alpha beta := ![s, r]
  let R := CommonRefinement.canonical D ha hb (fun i => (family i).seed)
  let g := s.representative.pullback (R.maps 0)
  let upper := r.representative.pullback (R.maps 1)
  have large : D.Holds R.seed (.member 0 1) ![g, upper] :=
    (GlobalTruth.member_at D ha hb family R 0 1).mp ((mem_mk D ha hb s r).mp edge)
  obtain ⟨f, preserve⟩ := g.clip_exists bound fallback inside
  have equivalent : D.RepEquivalent R.seed f.toRepresentative g := by
    apply (D.holds_mono R.seed (.member 0 1) (.equal 0 1) ![g, upper] ![f.toRepresentative, g] ?_) large
    intro x hx
    change (g.value x).val ∈ (upper.value x).val at hx
    change f.toRepresentative.value x = g.value x
    exact preserve x (transitive (upper.value x).val (upper.value_mem x) hx)
  refine ⟨encode bound ⟨R.seed, f⟩, ?_⟩
  rw [decode_encode]
  apply ((mk_same_seed_eq_iff D ha hb _ _ _).mpr equivalent).trans
  change mk D ha hb ⟨R.seed, s.representative.pullback (R.maps 0)⟩ = _
  rw [mk_pullback, R.projects 0]
  rfl

theorem covers (q : Ultrapower D ha hb) :
    ∃ bound fallback : stage.model.Element, ZFSet.IsTransitive bound.val ∧ fallback.val ∈ bound.val ∧
      ∃ c : SetDomain (domain stage alpha beta bound).val, decode D ha hb bound c = q := by
  classical
  obtain ⟨r, rfl⟩ := mk_surjective D ha hb q
  let bound := predecessorBound r
  have inside : (stage.ordinal 0).val ∈ bound.val := by
    rw [show bound = stage.hierarchy (Order.succ r.representative.range.val.rank) from rfl,
      stage.mem_hierarchy_iff]
    simp only [ModelStage.ordinal, Ordinal.rank_toZFSet]
    exact Order.lt_succ_of_le zero_le
  obtain ⟨f, preserve⟩ := r.representative.clip_exists bound (stage.ordinal 0) inside
  have equivalent : D.RepEquivalent r.seed f.toRepresentative r.representative := by
    apply D.holds_of_pointwise
    intro x
    change f.toRepresentative.value x = r.representative.value x
    apply preserve x
    apply (stage.mem_hierarchy_iff _ _).mpr
    exact (ZFSet.rank_lt_of_mem (r.representative.value_mem x)).trans (Order.lt_succ _)
  exact ⟨bound, stage.ordinal 0, stage.hierarchy_transitive _, inside, encode bound ⟨r.seed, f⟩,
    (decode_encode D ha hb bound _).trans ((mk_same_seed_eq_iff D ha hb _ _ _).mpr equivalent)⟩

end IBLP.Extender.LocalCodes
