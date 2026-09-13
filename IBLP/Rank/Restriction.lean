import FullMarkedBLP.RankPredicatePureFormula
import FullMarkedBLP.RankHierarchyImage

/-! 公式相对化参考 RankReflection/FormulaRelativization.lean。
本模块直接覆盖任意较小秩，包括本文必须使用的后继秩。 -/
namespace IBLP
open FullMarkedBLP

universe u

def rankInclude {alpha beta : Ordinal.{u}} (h : alpha ≤ beta) :
    RankDomain alpha → RankDomain beta := fun x => ⟨x.val, x.property.trans_le h⟩

/-- 用一个集合参数限制全部量词；它不是宇宙真谓词。 -/
def restrictFormula {n k : Nat} (phi : RankPredicateFormula 0 n)
    (indices : Fin n → Fin k) (domain : Fin k) : RankPredicateFormula 0 k :=
  match phi with
  | .falsum => .falsum
  | .equal x y => .equal (indices x) (indices y)
  | .member x y => .member (indices x) (indices y)
  | .predicate a _ => Fin.elim0 a
  | .imp p q => .imp (restrictFormula p indices domain) (restrictFormula q indices domain)
  | .all p => .all (.imp (.member (Fin.last k) domain.castSucc)
      (restrictFormula p (Fin.lastCases (Fin.last k) (fun i => (indices i).castSucc)) domain.castSucc))

theorem restrictFormula_realize {alpha beta : Ordinal.{u}} (hAB : alpha ≤ beta)
    {n k : Nat} (phi : RankPredicateFormula 0 n) (indices : Fin n → Fin k) (domain : Fin k)
    (values : Fin n → RankDomain alpha) (outer : Fin k → RankDomain beta)
    (hVars : ∀ i, (outer (indices i)).val = (values i).val)
    (hDomain : (outer domain).val = ZFSet.vonNeumann alpha) :
    (restrictFormula phi indices domain).Realize Fin.elim0 outer ↔
      phi.Realize Fin.elim0 values := by
  induction phi generalizing k with
  | falsum => rfl
  | equal x y =>
    change (outer (indices x) = outer (indices y)) ↔ values x = values y
    simp only [Subtype.ext_iff, hVars]
  | member x y =>
    change (outer (indices x)).val ∈ (outer (indices y)).val ↔ _
    rw [hVars, hVars]
    rfl
  | predicate a _ => exact Fin.elim0 a
  | imp p q ihp ihq =>
    exact imp_congr (ihp indices domain values outer hVars hDomain)
      (ihq indices domain values outer hVars hDomain)
  | @all n p ih =>
    simp only [restrictFormula, RankPredicateFormula.Realize, Fin.snoc_last, Fin.snoc_castSucc]
    change (∀ x : RankDomain beta, x.val ∈ (outer domain).val →
      (restrictFormula p (Fin.lastCases (Fin.last k) (fun i => (indices i).castSucc))
        domain.castSucc).Realize Fin.elim0 (Fin.snoc outer x)) ↔
      ∀ y : RankDomain alpha, p.Realize Fin.elim0 (Fin.snoc values y)
    have body (x : RankDomain beta) (y : RankDomain alpha) (hxy : x.val = y.val) :
        (restrictFormula p (Fin.lastCases (Fin.last k) (fun i => (indices i).castSucc))
          domain.castSucc).Realize Fin.elim0 (Fin.snoc outer x) ↔
          p.Realize Fin.elim0 (Fin.snoc values y) := by
      apply ih _ _ (Fin.snoc values y) (Fin.snoc outer x)
      · intro i
        cases i using Fin.lastCases with
        | last => simpa only [Fin.lastCases_last, Fin.snoc_last] using hxy
        | cast i => simpa only [Fin.lastCases_castSucc, Fin.snoc_castSucc] using hVars i
      · simpa only [Fin.snoc_castSucc] using hDomain
    constructor
    · intro h y
      let x := rankInclude hAB y
      apply (body x y rfl).mp
      apply h x
      rw [hDomain]
      exact ZFSet.mem_vonNeumann.mpr y.property
    · intro h x hx
      have hr : x.val.rank < alpha := ZFSet.mem_vonNeumann.mp (hDomain ▸ hx)
      exact (body x ⟨x.val, hr⟩ rfl).mpr (h ⟨x.val, hr⟩)

noncomputable def rankRestrictMap {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j : RankElementaryEmbedding lambda) (alpha : OrdinalDomain lambda) :
    RankDomain alpha.val → RankDomain (rankOrdinalAction j alpha).val := fun x =>
  let x' := rankInclude alpha.property.le x
  ⟨(j x').val, (rankElementary_rank_lt_iff hl j x' alpha).mpr x.property⟩

/-- 初等映射限制到 V_alpha 与 V_j(alpha) 后仍初等，包括 alpha 为后继的情况。 -/
noncomputable def rankRestrict {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j : RankElementaryEmbedding lambda) (alpha : OrdinalDomain lambda) :
    FirstOrder.Language.ElementaryEmbedding membershipLanguage
      (RankDomain alpha.val) (RankDomain (rankOrdinalAction j alpha).val) where
  toFun := rankRestrictMap hl j alpha
  map_formula' := by
    intro n phi values
    let p : RankPredicateFormula 0 n := rankPredicateOfFormula phi
    let outer : Fin (n + 1) → RankDomain lambda :=
      Fin.snoc (rankInclude alpha.property.le ∘ values) (rankHierarchy alpha)
    let q := restrictFormula p Fin.castSucc (Fin.last n)
    have source : q.Realize Fin.elim0 outer ↔ phi.Realize values := by
      rw [← rankPredicateOfFormula_realize (m := 0) phi Fin.elim0 values]
      apply restrictFormula_realize alpha.property.le
      · intro i
        simp only [outer, Fin.snoc_castSucc, Function.comp_apply, rankInclude]
      · simp only [outer, Fin.snoc_last, rankHierarchy]
    have target : q.Realize Fin.elim0 (j ∘ outer) ↔
        phi.Realize (rankRestrictMap hl j alpha ∘ values) := by
      rw [← rankPredicateOfFormula_realize (m := 0) phi Fin.elim0]
      apply restrictFormula_realize (rankOrdinalAction j alpha).property.le
      · intro i
        simp only [outer, Function.comp_apply, Fin.snoc_castSucc, rankRestrictMap]
      · simp only [outer, Function.comp_apply, Fin.snoc_last]
        rw [rankElementary_hierarchy hl]
        rfl
    exact target.symm.trans ((rankPredicate_elementary j q outer).trans source)

end IBLP
