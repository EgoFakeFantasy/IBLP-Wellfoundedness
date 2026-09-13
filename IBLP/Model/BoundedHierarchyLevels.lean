import IBLP.Model.BoundedHierarchy
import IBLP.Model.RankHierarchySequence

namespace IBLP
open FullMarkedBLP
universe u

namespace ModelStage

/-- A small internal recursion graph witnesses preservation of its levels by
an arbitrary elementary map between internal rank cuts. -/
theorem rankMap_hierarchy_below (stage : ModelStage.{u}) {alpha lambda mu : Ordinal.{u}}
    (ha : Order.IsSuccLimit alpha) (h : alpha ≤ lambda)
    (j : (stage.model.rankPart lambda).ElementaryMap (stage.model.rankPart mu))
    (eta : OrdinalDomain alpha) :
    j (stage.rankHierarchy (includeOrdinal h eta)) =
      stage.rankHierarchy (stage.rankOrdinalAction j (includeOrdinal h eta)) := by
  let upper : OrdinalDomain alpha := ⟨Order.succ eta.val, ha.succ_lt eta.property⟩
  have below : eta < upper := Order.lt_succ eta.val
  let graph := stage.hierarchyGraphIn ha h upper
  have function : (stage.model.rankPart mu).IsFunction (j graph)
      (j (stage.rankOrdinal (includeOrdinal h upper)))
      (j (stage.rankHierarchy (includeOrdinal h upper))) := by
    apply ((stage.model.rankPart mu).function_absolute _ _ _).mpr
    apply (j.function_iff _ _ _).mpr
    exact ((stage.model.rankPart lambda).function_absolute _ _ _).mp
      (stage.hierarchyGraphIn_function ha h upper)
  have ordinal := (j.isOrdinal_iff (stage.rankOrdinal (includeOrdinal h upper))).mpr
    (ZFSet.isOrdinal_toZFSet upper.val)
  have recursion := (j.hierarchyRec_iff graph).mpr (stage.hierarchyGraphIn_recursion ha h upper)
  have edge := (j.graphApplies_iff _ _ _).mpr (stage.hierarchyGraphIn_at ha h below)
  have member := (j.mem_iff (stage.rankOrdinal (includeOrdinal h eta))
    (stage.rankOrdinal (includeOrdinal h upper))).mpr (Ordinal.toZFSet_mem_toZFSet_iff.mpr below)
  apply Subtype.ext
  apply ZFSet.ext
  intro z
  have semantic := (stage.model.rankPart mu).hierarchyRec_mem_iff function ordinal recursion
    (stage.rankOrdinalAction j (includeOrdinal h eta)).val
    (j (stage.rankOrdinal (includeOrdinal h eta))) (j (stage.rankHierarchy (includeOrdinal h eta)))
    (stage.rankOrdinalAction_compat j (includeOrdinal h eta)) member edge z
  rw [semantic, stage.rankHierarchy_val, stage.mem_hierarchy]
  constructor
  · exact fun hz => ⟨hz.1.1, hz.2⟩
  · exact fun hz => ⟨⟨hz.1, hz.2.trans (stage.rankOrdinalAction j (includeOrdinal h eta)).property⟩, hz.2⟩

/-- Every level up through the source endpoint is preserved. The endpoint is
handled by its finite first-order characterization; smaller levels use the
actual hierarchy recursion graph. -/
theorem boundedMap_hierarchy (stage : ModelStage.{u}) {alpha beta : Ordinal.{u}}
    (ha : Order.IsSuccLimit alpha) (k : stage.BoundedMap alpha beta)
    (eta : OrdinalDomain (Order.succ alpha)) :
    k (stage.rankHierarchy eta) = stage.rankHierarchy (stage.rankOrdinalAction k eta) := by
  have he := Order.lt_succ_iff.mp eta.property
  rcases he.lt_or_eq with lower | same
  · exact stage.rankMap_hierarchy_below ha (Order.le_succ alpha) k ⟨eta.val, lower⟩
  · have hsame : eta = endpoint alpha := Subtype.ext same
    rw [hsame, stage.boundedMap_endpoint]
    exact stage.boundedMap_top k

end ModelStage
end IBLP
