import IBLP.Model.BoundedMap
import IBLP.Model.HierarchySequence
import IBLP.Rank.BoundedHierarchy

namespace IBLP
open FullMarkedBLP
universe u

theorem TransitiveClass.realize_or (M : TransitiveClass.{u}) {n : Nat}
    (p q : RankPredicateFormula 0 n) (values : Fin n → M.Element) :
    M.realize (p.or q) values ↔ M.realize p values ∨ M.realize q values := by
  classical
  simp [RankPredicateFormula.or, RankPredicateFormula.not, TransitiveClass.realize, imp_iff_not_or]

theorem TransitiveClass.rankFormulaOrdinal_realize (M : TransitiveClass.{u}) {n : Nat}
    (x : Fin n) (values : Fin n → M.Element) :
    M.realize (rankFormulaOrdinal x) values ↔ ZFSet.IsOrdinal (values x).val := by
  rw [rankFormulaOrdinal, M.realize_atom]
  have tuple : values ∘ ![x] = ![values x] := by funext i; fin_cases i; rfl
  rw [tuple, M.ordinalFormula_realize]

namespace ModelStage

theorem largestSetFormula_realize (stage : ModelStage.{u}) {alpha : Ordinal.{u}}
    (top : stage.model.RankElement (Order.succ alpha)) :
    (stage.model.rankPart (Order.succ alpha)).realize largestSetFormula ![top] ↔
      top.val = (stage.hierarchy alpha).val := by
  have semantics : (stage.model.rankPart (Order.succ alpha)).realize largestSetFormula ![top] ↔
      ∀ x y : stage.model.RankElement (Order.succ alpha), y.val ∈ x.val → y.val ∈ top.val := by
    simp [largestSetFormula, TransitiveClass.realize, Fin.snoc]
  rw [semantics]
  constructor
  · intro h
    apply ZFSet.ext
    intro z
    constructor
    · intro hz
      exact (stage.mem_hierarchy alpha z).mpr ⟨stage.model.transitive hz top.property.1,
        (ZFSet.rank_lt_of_mem hz).trans_le (Order.lt_succ_iff.mp top.property.2)⟩
    · intro hz
      obtain ⟨hm, hr⟩ := (stage.mem_hierarchy alpha z).mp hz
      let z' : stage.model.RankElement (Order.succ alpha) :=
        ⟨z, hm, hr.trans (Order.lt_succ alpha)⟩
      have singletonMember : ({z} : ZFSet.{u}) ∈ stage.model.carrier := by
        have hp := (stage.unorderedPair ⟨z, hm⟩ ⟨z, hm⟩).property
        simpa only [stage.unorderedPair_val, ZFSet.pair_eq_singleton] using hp
      let singleton : stage.model.RankElement (Order.succ alpha) := ⟨{z}, singletonMember, by
        rw [ZFSet.rank_singleton]
        exact Order.lt_succ_of_le (Order.succ_le_of_lt hr)⟩
      exact h singleton z' (by simp [singleton, z'])
  · intro same x y hy
    rw [same]
    exact (stage.mem_hierarchy alpha y.val).mpr ⟨y.property.1,
      (ZFSet.rank_lt_of_mem hy).trans_le (Order.lt_succ_iff.mp x.property.2)⟩

theorem boundedMap_top (stage : ModelStage.{u}) {alpha beta : Ordinal.{u}}
    (k : stage.BoundedMap alpha beta) :
    k (stage.rankHierarchy (endpoint alpha)) = stage.rankHierarchy (endpoint beta) := by
  have h := k.realize_iff largestSetFormula ![stage.rankHierarchy (endpoint alpha)]
  have same : k ∘ ![stage.rankHierarchy (endpoint alpha)] =
      ![k (stage.rankHierarchy (endpoint alpha))] := by funext i; fin_cases i; rfl
  rw [same, stage.largestSetFormula_realize, stage.largestSetFormula_realize] at h
  exact Subtype.ext (h.mpr rfl)

theorem largestOrdinalFormula_realize (stage : ModelStage.{u}) {alpha : Ordinal.{u}}
    (top : stage.model.RankElement (Order.succ alpha)) :
    (stage.model.rankPart (Order.succ alpha)).realize largestOrdinalFormula ![top] ↔
      top.val = alpha.toZFSet := by
  have semantics : (stage.model.rankPart (Order.succ alpha)).realize largestOrdinalFormula ![top] ↔
      ZFSet.IsOrdinal top.val ∧ ∀ x : stage.model.RankElement (Order.succ alpha),
        ZFSet.IsOrdinal x.val → x.val ∈ top.val ∨ x = top := by
    simp [largestOrdinalFormula, TransitiveClass.realize_and, TransitiveClass.realize,
      TransitiveClass.realize_or, TransitiveClass.rankFormulaOrdinal_realize]
  rw [semantics]
  constructor
  · rintro ⟨_, h⟩
    rcases h (stage.rankOrdinal (endpoint alpha)) (ZFSet.isOrdinal_toZFSet alpha) with hm | he
    · have hr := ZFSet.rank_lt_of_mem hm
      have bound := Order.lt_succ_iff.mp top.property.2
      simp only [stage.rankOrdinal_val, endpoint, Ordinal.rank_toZFSet] at hr
      exact False.elim ((not_lt_of_ge bound) hr)
    · exact (congrArg Subtype.val he).symm
  · intro same
    refine ⟨same ▸ ZFSet.isOrdinal_toZFSet alpha, ?_⟩
    intro x hx
    have bound := Order.lt_succ_iff.mp x.property.2
    rcases bound.lt_or_eq with hl | he
    · left
      rw [same, ← hx.toZFSet_rank_eq]
      exact Ordinal.toZFSet_mem_toZFSet_iff.mpr hl
    · right
      apply Subtype.ext
      rw [same]
      exact hx.toZFSet_rank_eq.symm.trans (congrArg Ordinal.toZFSet he)

theorem boundedMap_endpoint (stage : ModelStage.{u}) {alpha beta : Ordinal.{u}}
    (k : stage.BoundedMap alpha beta) :
    stage.rankOrdinalAction k (endpoint alpha) = endpoint beta := by
  have h := k.realize_iff largestOrdinalFormula ![stage.rankOrdinal (endpoint alpha)]
  have same : k ∘ ![stage.rankOrdinal (endpoint alpha)] =
      ![k (stage.rankOrdinal (endpoint alpha))] := by funext i; fin_cases i; rfl
  rw [same, stage.largestOrdinalFormula_realize, stage.largestOrdinalFormula_realize] at h
  apply Subtype.ext
  change (k (stage.rankOrdinal (endpoint alpha))).val.rank = beta
  rw [h.mpr rfl, Ordinal.rank_toZFSet]

end ModelStage
end IBLP
