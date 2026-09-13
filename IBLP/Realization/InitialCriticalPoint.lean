import IBLP.Model.GraphCriticalPoint
import IBLP.Realization.InitialGraph

namespace IBLP
open FullMarkedBLP
universe u

/-- The initial-model finite critical-point formula reads exactly the same
set graph as the original ambient root certificate. -/
theorem initial_graphCriticalPoint_iff {lambda : Ordinal.{u}}
    (graph : RankDomain lambda) (c : OrdinalDomain lambda) :
    initialStage.model.GraphCriticalPoint (initialElement graph.val) (initialStage.ordinal c.val) ↔
      GraphCriticalPoint graph c := by
  constructor
  · rintro ⟨_, ⟨y, hy, moved⟩, fixed⟩
    have edge := (initialStage.model.graphApplies_absolute _ _ _).mp hy
    have hy_rank : y.val.rank < lambda := by
      have h1 : y.val ∈ ({c.val.toZFSet, y.val} : ZFSet.{u}) := by simp
      have h2 : ({c.val.toZFSet, y.val} : ZFSet.{u}) ∈ ZFSet.pair c.val.toZFSet y.val := by
        simp [ZFSet.pair]
      exact (ZFSet.rank_lt_of_mem h1).trans ((ZFSet.rank_lt_of_mem h2).trans
        ((ZFSet.rank_lt_of_mem edge).trans graph.property))
    constructor
    · refine ⟨⟨y.val, hy_rank⟩, (graphApplies_absolute _ _ _).mpr edge, ?_⟩
      intro same
      exact moved (Subtype.ext (congrArg (fun z : RankDomain lambda => z.val) same))
    · intro a ha
      exact (graphApplies_absolute _ _ _).mpr
        ((initialStage.model.graphApplies_absolute _ _ _).mp
          (fixed (initialStage.ordinal a.val) (Ordinal.toZFSet_mem_toZFSet_iff.mpr ha)))
  · rintro ⟨⟨y, hy, moved⟩, fixed⟩
    refine ⟨ZFSet.isOrdinal_toZFSet c.val, ?_, ?_⟩
    · refine ⟨initialElement y.val, (initialStage.model.graphApplies_absolute _ _ _).mpr
        ((graphApplies_absolute _ _ _).mp hy), ?_⟩
      intro same
      exact moved (Subtype.ext (congrArg (fun z : initialStage.model.Element => z.val) same))
    · intro x hx
      obtain ⟨a, ha, same⟩ := Ordinal.mem_toZFSet_iff.mp hx
      have edge := (graphApplies_absolute _ _ _).mp (fixed ⟨a, ha.trans c.property⟩ ha)
      apply (initialStage.model.graphApplies_absolute _ _ _).mpr
      simpa only [ordinalDomainElement, same] using edge

end IBLP
