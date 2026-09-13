import IBLP.Realization.BoundedMapGraph

namespace IBLP
open FullMarkedBLP FirstOrder Language
universe u

namespace TransitiveClass

/-- The least moved ordinal, read from the actual set graph in the model. -/
def GraphCriticalPoint (M : TransitiveClass.{u}) (graph critical : M.Element) : Prop :=
  ZFSet.IsOrdinal critical.val ∧
    (∃ y : M.Element, M.GraphApplies graph critical y ∧ y ≠ critical) ∧
    ∀ x : M.Element, x.val ∈ critical.val → M.GraphApplies graph x x

end TransitiveClass

/-- Two parameters: the graph and the candidate critical ordinal. -/
def modelGraphCriticalPoint : RankPredicateFormula 0 2 :=
  (rankPredicateAtom rankOrdinalFormula ![1]).and
    (((rankPredicateAtom rankGraphAppliesFormula ![0, 1, 2]).and (.not (.equal 2 1))).ex.and
      (.all ((RankPredicateFormula.member 2 1).imp (rankPredicateAtom rankGraphAppliesFormula ![0, 2, 2]))))

def modelGraphCriticalPointFormula : membershipLanguage.Formula (Fin 2) :=
  rankPredicateToFormula modelGraphCriticalPoint

theorem modelGraphCriticalPoint_realize (M : TransitiveClass.{u}) (graph critical : M.Element) :
    M.realize modelGraphCriticalPoint ![graph, critical] ↔ M.GraphCriticalPoint graph critical := by
  simp only [modelGraphCriticalPoint, M.realize_and, M.realize_ex, M.realize_not,
    M.realize_atom, TransitiveClass.realize]
  have ordinalTuple : ![graph, critical] ∘ ![(1 : Fin 2)] = ![critical] := by
    funext i; fin_cases i; rfl
  have moveTuple (y : M.Element) : Fin.snoc ![graph, critical] y ∘ ![(0 : Fin 3), 1, 2] =
      ![graph, critical, y] := by funext i; fin_cases i <;> rfl
  have fixTuple (x : M.Element) : Fin.snoc ![graph, critical] x ∘ ![(0 : Fin 3), 2, 2] =
      ![graph, x, x] := by funext i; fin_cases i <;> rfl
  simp only [ordinalTuple, moveTuple, fixTuple, M.ordinalFormula_realize,
    M.graphAppliesFormula_realize]
  rfl

theorem modelGraphCriticalPointFormula_realize (M : TransitiveClass.{u})
    (graph critical : M.Element) :
    modelGraphCriticalPointFormula.Realize ![graph, critical] ↔ M.GraphCriticalPoint graph critical := by
  rw [modelGraphCriticalPointFormula, ← M.realize_toFormula, modelGraphCriticalPoint_realize]

theorem TransitiveClass.ElementaryMap.graphCriticalPoint_iff {M N : TransitiveClass.{u}}
    (j : M.ElementaryMap N) (graph critical : M.Element) :
    N.GraphCriticalPoint (j graph) (j critical) ↔ M.GraphCriticalPoint graph critical := by
  have h := j.realize_iff modelGraphCriticalPoint ![graph, critical]
  have tuple : j ∘ ![graph, critical] = ![j graph, j critical] := by
    funext i; fin_cases i <;> rfl
  simpa only [tuple, modelGraphCriticalPoint_realize] using h

namespace ModelStage

/-- For a represented bounded map the graph definition has exactly the
usual moves-and-fixes meaning. Its source bound is explicit. -/
theorem graphCriticalPoint_iff_boundedMap (stage : ModelStage.{u})
    {alpha beta : Ordinal.{u}} {graph : stage.model.Element} {k : stage.BoundedMap alpha beta}
    (represents : stage.RepresentsBoundedMap graph k) (c : Ordinal.{u}) (hc : c ≤ alpha) :
    stage.model.GraphCriticalPoint graph (stage.ordinal c) ↔
      (k (stage.rankOrdinal ⟨c, Order.lt_succ_of_le hc⟩)).val ≠ c.toZFSet ∧
      ∀ a : Ordinal.{u}, (ha : a < c) →
        (k (stage.rankOrdinal ⟨a, Order.lt_succ_of_le (ha.le.trans hc)⟩)).val = a.toZFSet := by
  constructor
  · rintro ⟨_, ⟨y, hy, moved⟩, fixed⟩
    constructor
    · intro same
      have edge := (stage.model.graphApplies_absolute _ _ _).mp hy
      have unique := (represents.1.2 c.toZFSet
        ((stage.ordinal_mem_hierarchy _ _).mpr (Order.lt_succ_of_le hc))).unique
        (represents.2 (stage.rankOrdinal ⟨c, Order.lt_succ_of_le hc⟩)) edge
      exact moved (Subtype.ext (unique.symm.trans same))
    · intro a ha
      have edge := (stage.model.graphApplies_absolute _ _ _).mp
        (fixed (stage.ordinal a) (Ordinal.toZFSet_mem_toZFSet_iff.mpr ha))
      exact (represents.1.2 a.toZFSet ((stage.ordinal_mem_hierarchy _ _).mpr
        (Order.lt_succ_of_le (ha.le.trans hc)))).unique
          (represents.2 (stage.rankOrdinal ⟨a, Order.lt_succ_of_le (ha.le.trans hc)⟩)) edge
  · rintro ⟨moved, fixed⟩
    refine ⟨ZFSet.isOrdinal_toZFSet c, ?_, ?_⟩
    · refine ⟨stage.rankInclude _ (k (stage.rankOrdinal ⟨c, Order.lt_succ_of_le hc⟩)),
        (stage.model.graphApplies_absolute _ _ _).mpr (represents.2 _), ?_⟩
      exact fun same => moved (congrArg Subtype.val same)
    · intro x hx
      obtain ⟨a, ha, same⟩ := Ordinal.mem_toZFSet_iff.mp hx
      apply (stage.model.graphApplies_absolute _ _ _).mpr
      have edge := represents.2 (stage.rankOrdinal ⟨a, Order.lt_succ_of_le (ha.le.trans hc)⟩)
      rw [fixed a ha] at edge
      simpa only [rankOrdinal_val, same] using edge

end ModelStage
end IBLP
