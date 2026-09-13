import IBLP.Extender.TupleDomains

namespace IBLP.Extender
open FullMarkedBLP
universe u

namespace Derivation
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}

/-- Every actual internal subset of a test support is itself in the source
successor rank. This discharges the rank bound instead of assuming it. -/
def subsetTest (support : Test stage alpha) (x : stage.model.Element) (inside : x.val ⊆ support.val) :
    Test stage alpha := ⟨x.val, x.property, (ZFSet.rank_mono inside).trans_lt support.property.2⟩

theorem meet_subset_left (x y : Test stage alpha) : (meet x y).val ⊆ x.val := by
  intro z hz
  rw [meet, stage.rankIntersection_val, ZFSet.mem_inter] at hz
  exact hz.1

/-- Restrict a derived measure to the actual internal subsets of a large
support. Both intersectands and the resulting measure are actual M-sets. -/
noncomputable def supportedMeasure (D : Derivation stage alpha beta) (seed : Seed stage beta)
    (support : Test stage alpha) : stage.model.Element :=
  stage.intersection (D.measure seed) (stage.powerset (stage.rankInclude _ support))

theorem mem_supportedMeasure_iff (D : Derivation stage alpha beta) (seed : Seed stage beta)
    (support x : Test stage alpha) :
    x.val ∈ (D.supportedMeasure seed support).val ↔ x.val ⊆ support.val ∧ D.Large seed x := by
  rw [supportedMeasure, stage.intersection_val, ZFSet.mem_inter, D.mem_measure_test_iff]
  have power := stage.mem_powerset (stage.rankInclude _ support) (stage.rankInclude _ x)
  exact (and_congr_right (fun _ => power)).trans and_comm

theorem supportedMeasure_support (D : Derivation stage alpha beta) (seed : Seed stage beta)
    (support : Test stage alpha) :
    (D.supportedMeasure seed support).val ⊆ (stage.powerset (stage.rankInclude _ support)).val := by
  intro x hx
  rw [supportedMeasure, stage.intersection_val, ZFSet.mem_inter] at hx
  exact hx.2

structure SupportedUltrafilter (support : Test stage alpha) (measure : stage.model.Element) : Prop where
  support_sets : measure.val ⊆ (stage.powerset (stage.rankInclude _ support)).val
  top_mem : support.val ∈ measure.val
  bottom_notMem : (bottom : Test stage alpha).val ∉ measure.val
  upward : ∀ x y : Test stage alpha,
    x.val ⊆ y.val → y.val ⊆ support.val → x.val ∈ measure.val → y.val ∈ measure.val
  meet_iff : ∀ x y : Test stage alpha,
    x.val ⊆ support.val → y.val ⊆ support.val →
    ((meet x y).val ∈ measure.val ↔ x.val ∈ measure.val ∧ y.val ∈ measure.val)
  compl_iff : ∀ x : Test stage alpha, x.val ⊆ support.val →
    ((meet support (compl x)).val ∈ measure.val ↔ x.val ∉ measure.val)

theorem supportedMeasure_ultrafilter (D : Derivation stage alpha beta) (seed : Seed stage beta)
    (support : Test stage alpha) (large : D.Large seed support) :
    SupportedUltrafilter support (D.supportedMeasure seed support) where
  support_sets := D.supportedMeasure_support seed support
  top_mem := (D.mem_supportedMeasure_iff seed support support).mpr ⟨fun _ h => h, large⟩
  bottom_notMem := fun h => D.not_large_bottom seed ((D.mem_supportedMeasure_iff seed support bottom).mp h).2
  upward := by
    intro x y hxy hys hx
    exact (D.mem_supportedMeasure_iff seed support y).mpr
      ⟨hys, D.large_mono seed hxy ((D.mem_supportedMeasure_iff seed support x).mp hx).2⟩
  meet_iff := by
    intro x y xs ys
    have subset : (meet x y).val ⊆ support.val := fun _ h => xs (meet_subset_left x y h)
    simp only [D.mem_supportedMeasure_iff, D.large_meet_iff, subset, xs, ys, true_and]
  compl_iff := by
    intro x inside
    rw [D.mem_supportedMeasure_iff, D.mem_supportedMeasure_iff]
    have subset := meet_subset_left support (compl x)
    rw [D.large_meet_iff, D.large_compl_iff]
    simp only [subset, inside, large, true_and]

/-- Manuscript (4.2), on the coded finite product. No external subsets are
silently inserted into the measure's domain. -/
noncomputable def tupleMeasure (D : Derivation stage alpha beta) (limit : Order.IsSuccLimit beta)
    {n : Nat} (seeds : Fin n → Seed stage beta) : stage.model.Element :=
  D.supportedMeasure (tupleSeed limit seeds) (tupleDomain n)

theorem mem_tupleMeasure_iff (D : Derivation stage alpha beta) (limit : Order.IsSuccLimit beta)
    {n : Nat} (seeds : Fin n → Seed stage beta) (x : Test stage alpha) :
    x.val ∈ (D.tupleMeasure limit seeds).val ↔
      x.val ⊆ (tupleDomain (stage := stage) (alpha := alpha) n).val ∧
        (tupleSeed limit seeds).val ∈ (D.map x).val :=
  D.mem_supportedMeasure_iff _ _ _

theorem tupleMeasure_ultrafilter (D : Derivation stage alpha beta) (limit : Order.IsSuccLimit beta)
    {n : Nat} (seeds : Fin n → Seed stage beta) :
    SupportedUltrafilter (tupleDomain (alpha := alpha) n) (D.tupleMeasure limit seeds) :=
  D.supportedMeasure_ultrafilter _ _ (D.large_tupleDomain limit seeds)

theorem tupleMeasure_subsets_iff (D : Derivation stage alpha beta) (limit : Order.IsSuccLimit beta)
    {n : Nat} (seeds : Fin n → Seed stage beta) (x : stage.model.Element)
    (inside : x.val ⊆ (tupleDomain (stage := stage) (alpha := alpha) n).val) :
    x.val ∈ (D.tupleMeasure limit seeds).val ↔
      (tupleSeed limit seeds).val ∈ (D.map (subsetTest (tupleDomain n) x inside)).val := by
  have h := D.mem_tupleMeasure_iff limit seeds (subsetTest (tupleDomain n) x inside)
  exact h.trans (and_iff_right inside)

/-- Coordinate pullback, restricted to the genuine finite product. -/
theorem tupleMeasure_coordinate_iff (D : Derivation stage alpha beta)
    (ha : Order.IsSuccLimit alpha) (hb : Order.IsSuccLimit beta)
    {n : Nat} (seeds : Fin n → Seed stage beta) (i : Fin n) (x : Test stage alpha) :
    (meet (tupleDomain n) (preimage (coordinate ha i) x)).val ∈ (D.tupleMeasure hb seeds).val ↔
      x.val ∈ (D.measure (seeds i)).val := by
  rw [D.mem_tupleMeasure_iff]
  have subset := meet_subset_left (tupleDomain n) (preimage (coordinate ha i) x)
  change (_ ∧ D.Large (tupleSeed hb seeds) (meet (tupleDomain n) (preimage (coordinate ha i) x))) ↔ _
  rw [D.large_meet_iff, D.large_preimage_iff, D.project_tupleSeed, D.mem_measure_test_iff]
  simp only [subset, D.large_tupleDomain hb seeds, true_and]

end Derivation
end IBLP.Extender
