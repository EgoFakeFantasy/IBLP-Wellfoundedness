import IBLP.Extender.DerivedMeasure

namespace IBLP.Extender
open FullMarkedBLP
universe u

namespace Derivation
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}

/-- Parameters are the saved graph and the set of source tests, followed
by the input seed and its entire measure. -/
def derivedMeasureMatrix : RankPredicateFormula 0 4 :=
  .all ((RankPredicateFormula.member 4 3).iff
    ((RankPredicateFormula.member 4 1).and (derivedLargeMatrix.relabelSets ![0, 2, 4])))

theorem derivedMeasureMatrix_realize (M : TransitiveClass.{u}) (graph tests seed measure : M.Element) :
    M.realize derivedMeasureMatrix (Fin.snoc (Fin.snoc ![graph, tests] seed) measure) ↔
      ∀ x : M.Element, x.val ∈ measure.val ↔ x.val ∈ tests.val ∧
        ∃ y : M.Element, ZFSet.pair x.val y.val ∈ graph.val ∧ seed.val ∈ y.val := by
  simp [derivedMeasureMatrix, RankPredicateFormula.iff, M.realize_and, M.realize_relabel,
    TransitiveClass.realize, derivedLargeMatrix, M.realize_ex, M.graphFormulaAtom_realize,
    iff_def, Fin.snoc, Function.comp_def]

theorem measure_matrix (D : Derivation stage alpha beta) (seed : Seed stage beta) :
    stage.model.realize derivedMeasureMatrix
      (Fin.snoc (Fin.snoc ![D.graph, stage.hierarchy (Order.succ alpha)]
        (stage.rankInclude _ seed)) (D.measure seed)) :=
  (derivedMeasureMatrix_realize _ _ _ _ _).mpr (D.mem_measure_iff seed)

/-- The entire seed-indexed family is a single actual set function in M.
Its construction uses a finite defining formula and internal Replacement. -/
theorem system_exists (D : Derivation stage alpha beta) :
    ∃ system : stage.model.Element,
      ZFSet.IsFunc (stage.hierarchy beta).val
        (stage.powerset (stage.hierarchy (Order.succ alpha))).val system.val ∧
      ∀ seed measure : stage.model.Element, ZFSet.pair seed.val measure.val ∈ system.val ↔
        seed.val ∈ (stage.hierarchy beta).val ∧ stage.model.realize derivedMeasureMatrix
          (Fin.snoc (Fin.snoc ![D.graph, stage.hierarchy (Order.succ alpha)] seed) measure) := by
  apply stage.definableGraph_exists derivedMeasureMatrix ![D.graph, stage.hierarchy (Order.succ alpha)]
  · intro seed hs
    let a : Seed stage beta := ⟨seed.val, (stage.mem_hierarchy beta seed.val).mp hs⟩
    refine ⟨D.measure a, ?_⟩
    exact D.measure_matrix a
  · intro seed measure _ hm
    apply (stage.mem_powerset _ _).mpr
    intro x hx
    exact ((derivedMeasureMatrix_realize _ _ _ _ _).mp hm
      (stage.model.member measure x hx) |>.mp hx).1
  · intro seed x y _ hx hy
    apply stage.model.element_ext
    intro z
    exact ((derivedMeasureMatrix_realize _ _ _ _ _).mp hx z).trans
      ((derivedMeasureMatrix_realize _ _ _ _ _).mp hy z).symm

noncomputable def system (D : Derivation stage alpha beta) : stage.model.Element := D.system_exists.choose

theorem system_function (D : Derivation stage alpha beta) :
    ZFSet.IsFunc (stage.hierarchy beta).val
      (stage.powerset (stage.hierarchy (Order.succ alpha))).val D.system.val :=
  D.system_exists.choose_spec.1

theorem system_edge_iff (D : Derivation stage alpha beta) (seed : Seed stage beta)
    (measure : stage.model.Element) :
    ZFSet.pair seed.val measure.val ∈ D.system.val ↔ measure = D.measure seed := by
  have edges := D.system_exists.choose_spec.2 (stage.rankInclude _ seed) measure
  constructor
  · intro edge
    have spec := (derivedMeasureMatrix_realize _ _ _ _ _).mp ((edges.mp edge).2)
    apply stage.model.element_ext
    intro x
    exact (spec x).trans (D.mem_measure_iff seed x).symm
  · intro same
    subst measure
    exact edges.mpr ⟨(stage.mem_hierarchy beta seed.val).mpr seed.property, D.measure_matrix seed⟩

theorem system_exact (D : Derivation stage alpha beta) (a e : ZFSet.{u}) :
    ZFSet.pair a e ∈ D.system.val ↔
      ∃ seed : Seed stage beta, seed.val = a ∧ (D.measure seed).val = e := by
  constructor
  · intro edge
    obtain ⟨ha, he⟩ := ZFSet.pair_mem_prod.mp (D.system_function.1 edge)
    let seed : Seed stage beta := ⟨a, (stage.mem_hierarchy beta a).mp ha⟩
    let measure := stage.model.member (stage.powerset (stage.hierarchy (Order.succ alpha))) e he
    exact ⟨seed, rfl, (congrArg Subtype.val ((D.system_edge_iff seed measure).mp edge)).symm⟩
  · rintro ⟨seed, rfl, rfl⟩
    exact (D.system_edge_iff seed _).mpr rfl

/-- Ultrafilter laws are stated on exactly M's actual subset algebra,
without extending the measure to arbitrary external subsets. -/
structure InternalUltrafilter (measure : stage.model.Element) : Prop where
  support : measure.val ⊆ (stage.hierarchy (Order.succ alpha)).val
  top_mem : (top : Test stage alpha).val ∈ measure.val
  bottom_notMem : (bottom : Test stage alpha).val ∉ measure.val
  upward : ∀ x y : Test stage alpha, x.val ⊆ y.val → x.val ∈ measure.val → y.val ∈ measure.val
  meet_iff : ∀ x y : Test stage alpha,
    (meet x y).val ∈ measure.val ↔ x.val ∈ measure.val ∧ y.val ∈ measure.val
  compl_iff : ∀ x : Test stage alpha, (compl x).val ∈ measure.val ↔ x.val ∉ measure.val

theorem measure_ultrafilter (D : Derivation stage alpha beta) (seed : Seed stage beta) :
    InternalUltrafilter (alpha := alpha) (D.measure seed) where
  support := D.measure_support seed
  top_mem := (D.mem_measure_test_iff seed top).mpr (D.large_top seed)
  bottom_notMem := fun h => D.not_large_bottom seed ((D.mem_measure_test_iff seed bottom).mp h)
  upward := by
    intro x y included large
    exact (D.mem_measure_test_iff seed y).mpr
      (D.large_mono seed included ((D.mem_measure_test_iff seed x).mp large))
  meet_iff := by
    intro x y
    simp only [D.mem_measure_test_iff, D.large_meet_iff]
  compl_iff := by
    intro x
    simp only [D.mem_measure_test_iff, D.large_compl_iff]

end Derivation
end IBLP.Extender
