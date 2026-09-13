import IBLP.Model.WeakAgreementFormula
import IBLP.Model.PairCoordinate

namespace IBLP.TransitiveClass
open FullMarkedBLP
universe u

theorem graphWeakMembership_external (M : IBLP.TransitiveClass.{u}) (graph source z x : M.Element) :
    M.realize graphWeakMembership ![graph, source, z, x] ↔
      ∃ t y : ZFSet.{u}, t = z.val ∩ source.val ∧ ZFSet.pair t y ∈ graph.val ∧ x.val ∈ y := by
  rw [graphWeakMembership_realize]
  constructor
  · rintro ⟨t, y, cut, edge, member⟩
    exact ⟨t.val, y.val, cut, edge, member⟩
  · rintro ⟨t, y, cut, edge, member⟩
    have contained := M.pair_components (M.transitive edge graph.property)
    exact ⟨⟨t, contained.1⟩, ⟨y, contained.2⟩, cut, edge, member⟩

/-- Both tested inputs are in the saved cutoff and all weak-value witnesses
are carried by the saved graphs. Their interpretation is thus absolute. -/
theorem graphWeakAgreement_external (M : IBLP.TransitiveClass.{u}) (f g sourceF sourceG cutoff : M.Element) :
    M.GraphWeakAgreement f g sourceF sourceG cutoff ↔
      ∀ x z : ZFSet.{u}, x ∈ cutoff.val → z ∈ cutoff.val →
        ((∃ t y : ZFSet.{u}, t = z ∩ sourceF.val ∧ ZFSet.pair t y ∈ f.val ∧ x ∈ y) ↔
          (∃ t y : ZFSet.{u}, t = z ∩ sourceG.val ∧ ZFSet.pair t y ∈ g.val ∧ x ∈ y)) := by
  unfold GraphWeakAgreement
  simp only [← graphWeakMembership_realize, M.graphWeakMembership_external]
  constructor
  · intro h x z hx hz
    exact h (M.member cutoff x hx) (M.member cutoff z hz) hx hz
  · intro h x z hx hz
    exact h x.val z.val hx hz

theorem graphWeakAgreement_absolute (M N : IBLP.TransitiveClass.{u})
    (f g sourceF sourceG cutoff : M.Element) (f' g' sourceF' sourceG' cutoff' : N.Element)
    (hf : f.val = f'.val) (hg : g.val = g'.val) (hsf : sourceF.val = sourceF'.val)
    (hsg : sourceG.val = sourceG'.val) (hc : cutoff.val = cutoff'.val) :
    M.GraphWeakAgreement f g sourceF sourceG cutoff ↔ N.GraphWeakAgreement f' g' sourceF' sourceG' cutoff' := by
  rw [M.graphWeakAgreement_external, N.graphWeakAgreement_external, hf, hg, hsf, hsg, hc]

end IBLP.TransitiveClass
