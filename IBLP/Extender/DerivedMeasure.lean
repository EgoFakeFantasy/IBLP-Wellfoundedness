import IBLP.Model.BooleanOperations
import IBLP.Model.BoundedHierarchy
import IBLP.Model.InternalWeakAction
import IBLP.Model.GraphOperations
import IBLP.Encoding.FiniteImage
import IBLP.Realization.BoundedMapGraph

namespace IBLP.Extender
open FullMarkedBLP
universe u

/-- The actual saved bounded graph from which the extender will be derived.
No global extension or ultrafilter existence is included in this input. -/
structure Derivation (stage : ModelStage.{u}) (alpha beta : Ordinal.{u}) where
  graph : stage.model.Element
  elementary : stage.InternalGraphElementary alpha beta graph

namespace Derivation
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}

noncomputable def map (D : Derivation stage alpha beta) : stage.BoundedMap alpha beta :=
  D.elementary.toRankEmbedding

theorem represents (D : Derivation stage alpha beta) : stage.RepresentsBoundedMap D.graph D.map :=
  ModelStage.RepresentsBoundedMap.of_internalGraphElementary D.elementary

abbrev Test (stage : ModelStage.{u}) (alpha : Ordinal.{u}) :=
  stage.model.RankElement (Order.succ alpha)

abbrev Seed (stage : ModelStage.{u}) (beta : Ordinal.{u}) := stage.model.RankElement beta

def Large (D : Derivation stage alpha beta) (seed : Seed stage beta) (x : Test stage alpha) : Prop :=
  seed.val ∈ (D.map x).val

noncomputable def top : Test stage alpha := stage.rankHierarchy (endpoint alpha)
noncomputable def bottom : Test stage alpha :=
  stage.rankOrdinal ⟨0, Order.lt_succ_of_le (show (0 : Ordinal.{u}) ≤ alpha from zero_le)⟩

theorem test_subset (x : Test stage alpha) : x.val ⊆ (stage.hierarchy alpha).val := by
  intro z hz
  exact (stage.mem_hierarchy alpha z).mpr ⟨stage.model.transitive hz x.property.1,
    (ZFSet.rank_lt_of_mem hz).trans_le (Order.lt_succ_iff.mp x.property.2)⟩

noncomputable def meet (x y : Test stage alpha) : Test stage alpha := stage.rankIntersection x y

noncomputable def compl (x : Test stage alpha) : Test stage alpha :=
  ⟨(stage.difference (stage.hierarchy alpha) (stage.rankInclude _ x)).val,
    (stage.difference (stage.hierarchy alpha) (stage.rankInclude _ x)).property, by
      apply Order.lt_succ_of_le
      apply (ZFSet.rank_mono (show (stage.difference (stage.hierarchy alpha) (stage.rankInclude _ x)).val ⊆
          (stage.hierarchy alpha).val from ?_)).trans_eq (stage.hierarchy_rank alpha)
      intro z hz
      rw [stage.difference_val, ZFSet.mem_sep] at hz
      exact hz.1⟩

theorem compl_val (x : Test stage alpha) :
    (compl x).val = ZFSet.sep (fun z => z ∉ x.val) (stage.hierarchy alpha).val :=
  stage.difference_val _ _

theorem large_top (D : Derivation stage alpha beta) (seed : Seed stage beta) : D.Large seed top := by
  change seed.val ∈ (D.map (stage.rankHierarchy (endpoint alpha))).val
  rw [stage.boundedMap_top]
  exact (stage.mem_hierarchy beta seed.val).mpr seed.property

theorem not_large_bottom (D : Derivation stage alpha beta) (seed : Seed stage beta) :
    ¬D.Large seed bottom := by
  have h := D.map.map_formula rankEmptyFormula ![bottom]
  have args : D.map ∘ ![bottom] = ![D.map bottom] := by funext i; fin_cases i; rfl
  rw [args, (stage.model.rankPart (Order.succ alpha)).emptyFormula_realize,
    (stage.model.rankPart (Order.succ beta)).emptyFormula_realize] at h
  have empty := h.mpr (by simp [bottom])
  change seed.val ∉ (D.map bottom).val
  rw [empty]
  exact ZFSet.notMem_empty _

theorem large_mono (D : Derivation stage alpha beta) (seed : Seed stage beta)
    {x y : Test stage alpha} (included : x.val ⊆ y.val) (large : D.Large seed x) : D.Large seed y :=
  (D.map.subset_iff x y).mpr included large

theorem large_meet_iff (D : Derivation stage alpha beta) (seed : Seed stage beta) (x y : Test stage alpha) :
    D.Large seed (meet x y) ↔ D.Large seed x ∧ D.Large seed y := by
  change seed.val ∈ (D.map (stage.rankIntersection x y)).val ↔ _
  rw [stage.rankMap_intersection, stage.rankIntersection_val, ZFSet.mem_inter]
  rfl

theorem large_compl_iff (D : Derivation stage alpha beta) (seed : Seed stage beta) (x : Test stage alpha) :
    D.Large seed (compl x) ↔ ¬D.Large seed x := by
  have image := (D.map.difference_iff (compl x) top x).mpr (compl_val x)
  change seed.val ∈ (D.map (compl x)).val ↔ seed.val ∉ (D.map x).val
  rw [image, ZFSet.mem_sep]
  exact and_iff_right (D.large_top seed)

theorem large_nonempty (D : Derivation stage alpha beta) (seed : Seed stage beta)
    {x : Test stage alpha} (large : D.Large seed x) : ∃ z, z ∈ x.val := by
  by_contra h
  have empty : x.val = ∅ := (ZFSet.eq_empty _).mpr (by simpa using h)
  have same : x = bottom := Subtype.ext (by simpa [bottom] using empty)
  exact D.not_large_bottom seed (same ▸ large)

/-- One finite formula, with graph and seed parameters, selects the large
subsets among the actual members of the saved source successor rank. -/
def derivedLargeMatrix : RankPredicateFormula 0 3 :=
  ((rankPredicateAtom rankGraphAppliesFormula ![0, 2, 3]).and (.member 1 3)).ex

theorem derivedLargeMatrix_realize (M : TransitiveClass.{u}) (graph seed x : M.Element) :
    M.realize derivedLargeMatrix ![graph, seed, x] ↔
      ∃ y : M.Element, ZFSet.pair x.val y.val ∈ graph.val ∧ seed.val ∈ y.val := by
  simp [derivedLargeMatrix, M.realize_ex, M.realize_and, M.graphFormulaAtom_realize,
    TransitiveClass.realize]

noncomputable def measure (D : Derivation stage alpha beta) (seed : Seed stage beta) : stage.model.Element :=
  stage.separation derivedLargeMatrix ![D.graph, stage.rankInclude _ seed]
    (stage.hierarchy (Order.succ alpha))

theorem mem_measure_iff (D : Derivation stage alpha beta) (seed : Seed stage beta)
    (x : stage.model.Element) :
    x.val ∈ (D.measure seed).val ↔ x.val ∈ (stage.hierarchy (Order.succ alpha)).val ∧
      ∃ y : stage.model.Element, ZFSet.pair x.val y.val ∈ D.graph.val ∧ seed.val ∈ y.val := by
  rw [measure, stage.mem_separation]
  have args : Fin.snoc ![D.graph, stage.rankInclude _ seed] x = ![D.graph, stage.rankInclude _ seed, x] := by
    funext i; fin_cases i <;> rfl
  rw [args, derivedLargeMatrix_realize]
  rfl

theorem mem_measure_test_iff (D : Derivation stage alpha beta) (seed : Seed stage beta)
    (x : Test stage alpha) : x.val ∈ (D.measure seed).val ↔ D.Large seed x := by
  change (stage.rankInclude _ x).val ∈ (D.measure seed).val ↔ _
  rw [D.mem_measure_iff]
  constructor
  · rintro ⟨_, y, edge, hy⟩
    obtain ⟨z, hz, image⟩ := (D.represents.graph_exact _ _).mp edge
    have same : z = x := Subtype.ext hz
    change seed.val ∈ (D.map x).val
    rw [same] at image
    rw [image]
    exact hy
  · intro large
    exact ⟨(stage.mem_hierarchy _ x.val).mpr x.property,
      stage.rankInclude _ (D.map x), D.represents.2 x, large⟩

theorem measure_support (D : Derivation stage alpha beta) (seed : Seed stage beta) :
    (D.measure seed).val ⊆ (stage.hierarchy (Order.succ alpha)).val := by
  intro x hx
  exact ((D.mem_measure_iff seed (stage.model.member (D.measure seed) x hx)).mp hx).1

end Derivation
end IBLP.Extender
