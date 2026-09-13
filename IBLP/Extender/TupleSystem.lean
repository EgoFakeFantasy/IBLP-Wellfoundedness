import IBLP.Extender.TupleMeasure
import IBLP.Model.CountableImage

namespace IBLP.Extender
open FullMarkedBLP
universe u

namespace Derivation
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}

/-- Parameters are graph, all tests, allowed tests, input seed, and measure. -/
def supportedMeasureMatrix : RankPredicateFormula 0 5 :=
  .all ((RankPredicateFormula.member 5 4).iff
    ((RankPredicateFormula.member 5 1).and
      ((RankPredicateFormula.member 5 2).and (derivedLargeMatrix.relabelSets ![0, 3, 5]))))

theorem supportedMeasureMatrix_realize (M : TransitiveClass.{u})
    (graph tests allowed seed measure : M.Element) :
    M.realize supportedMeasureMatrix (Fin.snoc (Fin.snoc ![graph, tests, allowed] seed) measure) ↔
      ∀ x : M.Element, x.val ∈ measure.val ↔ x.val ∈ tests.val ∧ x.val ∈ allowed.val ∧
        ∃ y : M.Element, ZFSet.pair x.val y.val ∈ graph.val ∧ seed.val ∈ y.val := by
  simp [supportedMeasureMatrix, RankPredicateFormula.iff, M.realize_and, M.realize_relabel,
    TransitiveClass.realize, derivedLargeMatrix, M.realize_ex, M.graphFormulaAtom_realize,
    iff_def, Fin.snoc, Function.comp_def]

theorem supportedMeasure_matrix (D : Derivation stage alpha beta) (seed : Seed stage beta)
    (support : Test stage alpha) : stage.model.realize supportedMeasureMatrix
      (Fin.snoc (Fin.snoc ![D.graph, stage.hierarchy (Order.succ alpha),
        stage.powerset (stage.rankInclude _ support)] (stage.rankInclude _ seed))
          (D.supportedMeasure seed support)) := by
  apply (supportedMeasureMatrix_realize _ _ _ _ _ _).mpr
  intro x
  rw [supportedMeasure, stage.intersection_val, ZFSet.mem_inter, D.mem_measure_iff]
  tauto

theorem tupleFamily_exists (D : Derivation stage alpha beta) (n : Nat) :
    ∃ family : stage.model.Element,
      ZFSet.IsFunc (tupleDomain (stage := stage) (alpha := beta) n).val
        (stage.powerset (stage.hierarchy (Order.succ alpha))).val family.val ∧
      ∀ seed measure : stage.model.Element, ZFSet.pair seed.val measure.val ∈ family.val ↔
        seed.val ∈ (tupleDomain (stage := stage) (alpha := beta) n).val ∧
          stage.model.realize supportedMeasureMatrix
            (Fin.snoc (Fin.snoc ![D.graph, stage.hierarchy (Order.succ alpha),
              stage.powerset (stage.rankInclude _ (tupleDomain (alpha := alpha) n))] seed) measure) := by
  apply stage.definableGraph_exists supportedMeasureMatrix
    ![D.graph, stage.hierarchy (Order.succ alpha),
      stage.powerset (stage.rankInclude _ (tupleDomain n))]
  · intro seed hs
    have inside := ((mem_tupleDomain n seed.val).mp hs).1
    let a : Seed stage beta := ⟨seed.val, (stage.mem_hierarchy beta seed.val).mp inside⟩
    exact ⟨D.supportedMeasure a (tupleDomain n), D.supportedMeasure_matrix a (tupleDomain n)⟩
  · intro seed measure _ hm
    apply (stage.mem_powerset _ _).mpr
    intro x hx
    exact ((supportedMeasureMatrix_realize _ _ _ _ _ _).mp hm
      (stage.model.member measure x hx) |>.mp hx).1
  · intro seed x y _ hx hy
    apply stage.model.element_ext
    intro z
    exact ((supportedMeasureMatrix_realize _ _ _ _ _ _).mp hx z).trans
      ((supportedMeasureMatrix_realize _ _ _ _ _ _).mp hy z).symm

noncomputable def tupleFamily (D : Derivation stage alpha beta) (n : Nat) : stage.model.Element :=
  (D.tupleFamily_exists n).choose

theorem tupleFamily_function (D : Derivation stage alpha beta) (n : Nat) :
    ZFSet.IsFunc (tupleDomain (stage := stage) (alpha := beta) n).val
      (stage.powerset (stage.hierarchy (Order.succ alpha))).val (D.tupleFamily n).val :=
  (D.tupleFamily_exists n).choose_spec.1

theorem tupleFamily_edge_iff (D : Derivation stage alpha beta) (limit : Order.IsSuccLimit beta)
    {n : Nat} (seeds : Fin n → Seed stage beta) (measure : stage.model.Element) :
    ZFSet.pair (tupleSeed limit seeds).val measure.val ∈ (D.tupleFamily n).val ↔
      measure = D.tupleMeasure limit seeds := by
  let seed := tupleSeed limit seeds
  have edges := (D.tupleFamily_exists n).choose_spec.2 (stage.rankInclude _ seed) measure
  constructor
  · intro edge
    have spec := (supportedMeasureMatrix_realize _ _ _ _ _ _).mp ((edges.mp edge).2)
    have expected := (supportedMeasureMatrix_realize _ _ _ _ _ _).mp
      (D.supportedMeasure_matrix seed (tupleDomain n))
    apply stage.model.element_ext
    intro x
    exact (spec x).trans (expected x).symm
  · intro same
    subst measure
    exact edges.mpr ⟨tupleSeed_mem_tupleDomain limit seeds, D.supportedMeasure_matrix seed (tupleDomain n)⟩

/-- The complete finite-arity system is one actual set in M, represented as
an omega-indexed array of seed-to-measure graphs. The arity collection uses
the already maintained external countable closure of the current model. -/
noncomputable def extenderSet (D : Derivation stage alpha beta) : stage.model.Element :=
  stage.countableGraph D.tupleFamily

theorem extenderSet_function (D : Derivation stage alpha beta) :
    ZFSet.IsFunc (stage.ordinal Ordinal.omega0).val (stage.countableRange D.tupleFamily).val D.extenderSet.val :=
  stage.countableGraph_function D.tupleFamily

theorem extenderSet_arity_iff (D : Derivation stage alpha beta) (n : Nat) (family : ZFSet.{u}) :
    ZFSet.pair (n : Ordinal.{u}).toZFSet family ∈ D.extenderSet.val ↔ family = (D.tupleFamily n).val := by
  constructor
  · intro edge
    obtain ⟨m, same⟩ := ZFSet.mem_range.mp edge
    obtain ⟨index, value⟩ := ZFSet.pair_inj.mp same
    have sameIndex : m = n := Nat.cast_injective (Ordinal.toZFSet_injective index)
    simpa only [sameIndex] using value.symm
  · intro same
    subst family
    exact ZFSet.mem_range.mpr ⟨n, rfl⟩

/-- Exact decoding of the single internal extender set at every arity and
every genuine finite seed tuple, giving precisely the original derived test. -/
theorem extenderSet_test_iff (D : Derivation stage alpha beta) (limit : Order.IsSuccLimit beta)
    {n : Nat} (seeds : Fin n → Seed stage beta) (x : Test stage alpha) :
    (∃ family measure : stage.model.Element,
      ZFSet.pair (n : Ordinal.{u}).toZFSet family.val ∈ D.extenderSet.val ∧
      ZFSet.pair (tupleSeed limit seeds).val measure.val ∈ family.val ∧ x.val ∈ measure.val) ↔
      x.val ⊆ (tupleDomain (stage := stage) (alpha := alpha) n).val ∧
        (tupleSeed limit seeds).val ∈ (D.map x).val := by
  rw [← D.mem_tupleMeasure_iff limit seeds x]
  constructor
  · rintro ⟨family, measure, outer, inner, member⟩
    have familyEq := (D.extenderSet_arity_iff n family.val).mp outer
    rw [familyEq] at inner
    have measureEq := (D.tupleFamily_edge_iff limit seeds measure).mp inner
    simpa only [measureEq] using member
  · intro member
    exact ⟨D.tupleFamily n, D.tupleMeasure limit seeds, (D.extenderSet_arity_iff n _).mpr rfl,
      (D.tupleFamily_edge_iff limit seeds _).mpr rfl, member⟩

end Derivation
end IBLP.Extender
