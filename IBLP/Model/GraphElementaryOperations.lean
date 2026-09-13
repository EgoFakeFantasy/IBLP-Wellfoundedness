import IBLP.Model.GraphOperations

namespace IBLP
open FullMarkedBLP FirstOrder Language
universe u

/-- Matching internal elementary graphs compose to an actual internal
elementary graph, with precisely the composite elementary embedding. -/
theorem ModelStage.compGraph_elementary (stage : ModelStage.{u})
    (f g domain middle range : stage.model.Element)
    (hf : stage.model.GraphElementary f domain middle)
    (hg : stage.model.GraphElementary g middle range) :
    stage.model.GraphElementary
      (stage.compGraph f g domain middle middle range
        ((stage.model.function_absolute _ _ _).mp hf.1)
        ((stage.model.function_absolute _ _ _).mp hg.1) (fun _ h => h)) domain range := by
  let ff := (stage.model.function_absolute _ _ _).mp hf.1
  let gf := (stage.model.function_absolute _ _ _).mp hg.1
  apply TransitiveClass.GraphElementary.of_embedding
    ((stage.model.function_absolute _ _ _).mpr (stage.compGraph_function f g domain middle middle range ff gf (fun _ h => h)))
    (hg.toEmbedding.comp hf.toEmbedding)
  intro x z
  rw [stage.model.graphApplies_absolute, stage.compGraph_edge_iff]
  constructor
  · rintro ⟨y, first, second⟩
    have ym : y ∈ middle.val := (ZFSet.pair_mem_prod.mp (ff.1 first)).2
    let y' : SetDomain middle.val := ⟨y, ym⟩
    have firstEq : hf.toEmbedding x = y' :=
      (hf.applies_iff x y').mp ((stage.model.graphApplies_absolute _ _ _).mpr first)
    have secondEq : hg.toEmbedding y' = z :=
      (hg.applies_iff y' z).mp ((stage.model.graphApplies_absolute _ _ _).mpr second)
    change hg.toEmbedding (hf.toEmbedding x) = z
    rw [firstEq, secondEq]
  · intro image
    refine ⟨(hf.toEmbedding x).val, ?_, ?_⟩
    · exact (stage.model.graphApplies_absolute _ _ _).mp (hf.value_applies x)
    · have second := (stage.model.graphApplies_absolute _ _ _).mp (hg.value_applies (hf.toEmbedding x))
      change hg.toEmbedding (hf.toEmbedding x) = z at image
      change ZFSet.pair (hf.toEmbedding x).val (hg.toEmbedding (hf.toEmbedding x)).val ∈ g.val at second
      rw [image] at second
      exact second

/-- The elementary map recovered from the constructed graph is exactly the
composition of the maps recovered from its factors. -/
theorem ModelStage.compGraph_toEmbedding (stage : ModelStage.{u})
    (f g domain middle range : stage.model.Element)
    (hf : stage.model.GraphElementary f domain middle)
    (hg : stage.model.GraphElementary g middle range) (x : SetDomain domain.val) :
    (stage.compGraph_elementary f g domain middle range hf hg).toEmbedding x =
      hg.toEmbedding (hf.toEmbedding x) := by
  apply ((stage.compGraph_elementary f g domain middle range hf hg).applies_iff _ _).mp
  apply (stage.model.graphApplies_absolute _ _ _).mpr
  apply (stage.compGraph_edge_iff _ _ _ _ _ _ _ _ _ _ _).mpr
  exact ⟨(hf.toEmbedding x).val,
    (stage.model.graphApplies_absolute _ _ _).mp (hf.value_applies x),
    (stage.model.graphApplies_absolute _ _ _).mp (hg.value_applies (hf.toEmbedding x))⟩

end IBLP
