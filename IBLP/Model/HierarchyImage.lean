import IBLP.Model.Hierarchy

namespace IBLP
open FullMarkedBLP FirstOrder Language
universe u

theorem TransitiveClass.ElementaryMap.graphApplies_iff {M N : TransitiveClass.{u}}
    (j : M.ElementaryMap N) (graph input output : M.Element) :
    N.GraphApplies (j graph) (j input) (j output) ↔ M.GraphApplies graph input output := by
  have h := j.map_formula rankGraphAppliesFormula ![graph, input, output]
  have tuple : j ∘ ![graph, input, output] = ![j graph, j input, j output] := by
    funext i; fin_cases i <;> rfl
  rw [tuple, N.graphAppliesFormula_realize, M.graphAppliesFormula_realize] at h
  exact h

/-- The ordinal action of an actual elementary map out of a model stage. -/
noncomputable def ModelStage.ordinalImage (source : ModelStage.{u})
    {N : TransitiveClass.{u}} (j : source.model.ElementaryMap N) (beta : Ordinal.{u}) :
    Ordinal.{u} := (j (source.ordinal beta)).val.rank

theorem ModelStage.ordinalImage_compat (source : ModelStage.{u}) {N : TransitiveClass.{u}}
    (j : source.model.ElementaryMap N) (beta : Ordinal.{u}) :
    (j (source.ordinal beta)).val = (source.ordinalImage j beta).toZFSet :=
  ((j.isOrdinal_iff _).mpr (ZFSet.isOrdinal_toZFSet beta)).toZFSet_rank_eq.symm

theorem ModelStage.ordinalImage_strictMono (source : ModelStage.{u}) {N : TransitiveClass.{u}}
    (j : source.model.ElementaryMap N) : StrictMono (source.ordinalImage j) := by
  intro alpha beta smaller
  rw [← Ordinal.toZFSet_mem_toZFSet_iff, ← source.ordinalImage_compat, ← source.ordinalImage_compat]
  exact (j.mem_iff _ _).mpr (Ordinal.toZFSet_mem_toZFSet_iff.mpr smaller)

theorem ModelStage.ordinalImage_le (source : ModelStage.{u}) {N : TransitiveClass.{u}}
    (j : source.model.ElementaryMap N) (beta : Ordinal.{u}) :
    beta ≤ source.ordinalImage j beta := (source.ordinalImage_strictMono j).le_apply

/-- Cumulative levels are preserved by actual elementary maps between stages.
The source graph is transported as a set, and its target value is identified
using the model-relative hierarchy recursion. -/
theorem ModelStage.hierarchy_image (source target : ModelStage.{u})
    (j : source.model.ElementaryMap target.model) (beta : Ordinal.{u}) :
    j (source.hierarchy beta) = target.hierarchy (source.ordinalImage j beta) := by
  obtain ⟨range, graph, function, recursion⟩ :=
    source.hierarchy_graph_exists (source.ordinal (Order.succ beta)) (ZFSet.isOrdinal_toZFSet _)
  have member : (source.ordinal beta).val ∈ (source.ordinal (Order.succ beta)).val :=
    Ordinal.toZFSet_mem_toZFSet_iff.mpr (Order.lt_succ beta)
  obtain ⟨value, _, edge, _⟩ := function.2 (source.ordinal beta) member
  have valueEq : value = source.hierarchy beta := by
    apply Subtype.ext
    apply ZFSet.ext
    intro z
    rw [source.mem_hierarchy]
    exact source.model.hierarchyRec_mem_iff function (ZFSet.isOrdinal_toZFSet _) recursion beta
      (source.ordinal beta) value rfl member edge z
  have targetFunction : target.model.IsFunction (j graph)
      (j (source.ordinal (Order.succ beta))) (j range) := by
    apply (target.model.function_absolute _ _ _).mpr
    apply (j.function_iff _ _ _).mpr
    exact (source.model.function_absolute _ _ _).mp function
  have targetOrdinal : ZFSet.IsOrdinal (j (source.ordinal (Order.succ beta))).val :=
    (j.isOrdinal_iff _).mpr (ZFSet.isOrdinal_toZFSet _)
  have targetRecursion := (j.hierarchyRec_iff graph).mpr recursion
  have targetMember := (j.mem_iff _ _).mpr member
  have targetEdge := (j.graphApplies_iff _ _ _).mpr edge
  rw [← valueEq]
  apply Subtype.ext
  apply ZFSet.ext
  intro z
  rw [target.mem_hierarchy]
  exact target.model.hierarchyRec_mem_iff targetFunction targetOrdinal targetRecursion
    (source.ordinalImage j beta) (j (source.ordinal beta)) (j value)
    (source.ordinalImage_compat j beta) targetMember targetEdge z

end IBLP
