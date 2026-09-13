import IBLP.Model.Relativization
import IBLP.Model.Graph

namespace IBLP
open FullMarkedBLP FirstOrder Language
universe u

namespace TransitiveClass

/-- 实际模型内的集合函数图及其全部有限相对化公式的保持方案。
这一定义不宣称已经把全公式量化编码为单个集合论公式。 -/
def GraphElementary (M : TransitiveClass.{u}) (graph domain range : M.Element) : Prop :=
  M.IsFunction graph domain range ∧
  ∀ (n : Nat) (phi : membershipLanguage.Formula (Fin n))
    (xs : Fin n → SetDomain domain.val) (ys : Fin n → SetDomain range.val),
    (∀ i, M.GraphApplies graph (M.setInclude domain (xs i)) (M.setInclude range (ys i))) →
    (M.realize (setFormula phi) (Fin.snoc (M.setInclude range ∘ ys) range) ↔
      M.realize (setFormula phi) (Fin.snoc (M.setInclude domain ∘ xs) domain))

theorem GraphElementary.output_exists {M : TransitiveClass.{u}} {graph domain range : M.Element}
    (h : M.GraphElementary graph domain range) (x : SetDomain domain.val) :
    ∃ y : SetDomain range.val, M.GraphApplies graph (M.setInclude domain x) (M.setInclude range y) := by
  obtain ⟨y, hy, hedge, _⟩ := h.1.2 (M.setInclude domain x) x.property
  exact ⟨⟨y.val, hy⟩, hedge⟩

noncomputable def GraphElementary.value {M : TransitiveClass.{u}} {graph domain range : M.Element}
    (h : M.GraphElementary graph domain range) (x : SetDomain domain.val) : SetDomain range.val :=
  (h.output_exists x).choose

theorem GraphElementary.value_applies {M : TransitiveClass.{u}} {graph domain range : M.Element}
    (h : M.GraphElementary graph domain range) (x : SetDomain domain.val) :
    M.GraphApplies graph (M.setInclude domain x) (M.setInclude range (h.value x)) :=
  (h.output_exists x).choose_spec

theorem GraphElementary.value_unique {M : TransitiveClass.{u}} {graph domain range : M.Element}
    (h : M.GraphElementary graph domain range) (x : SetDomain domain.val) (y : SetDomain range.val)
    (hy : M.GraphApplies graph (M.setInclude domain x) (M.setInclude range y)) : y = h.value x := by
  obtain ⟨z, _, _, unique⟩ := h.1.2 (M.setInclude domain x) x.property
  apply Subtype.ext
  exact congrArg (fun z : M.Element => z.val)
    ((unique _ hy).trans (unique _ (h.value_applies x)).symm)

/-- 初等映射直接由图的唯一取值恢复，不引入任何全域 owner。 -/
noncomputable def GraphElementary.toEmbedding {M : TransitiveClass.{u}}
    {graph domain range : M.Element} (h : M.GraphElementary graph domain range) :
    ElementaryEmbedding membershipLanguage (SetDomain domain.val) (SetDomain range.val) where
  toFun := h.value
  map_formula' := by
    intro n phi xs
    have hs := h.2 n phi xs (h.value ∘ xs) (fun i => h.value_applies (xs i))
    rwa [M.setFormula_realize, M.setFormula_realize] at hs

theorem GraphElementary.applies_iff {M : TransitiveClass.{u}} {graph domain range : M.Element}
    (h : M.GraphElementary graph domain range) (x : SetDomain domain.val) (y : SetDomain range.val) :
    M.GraphApplies graph (M.setInclude domain x) (M.setInclude range y) ↔ h.toEmbedding x = y := by
  constructor
  · exact fun he => (h.value_unique x y he).symm
  · intro he
    simpa only [← he] using h.value_applies x

/-- 给定一个实际初等映射及其完整集合图，恢复同一模型中的图初等性。 -/
theorem GraphElementary.of_embedding {M : TransitiveClass.{u}} {graph domain range : M.Element}
    (isFunction : M.IsFunction graph domain range)
    (j : ElementaryEmbedding membershipLanguage (SetDomain domain.val) (SetDomain range.val))
    (edges : ∀ x y, M.GraphApplies graph (M.setInclude domain x) (M.setInclude range y) ↔ j x = y) :
    M.GraphElementary graph domain range := by
  refine ⟨isFunction, ?_⟩
  intro n phi xs ys hs
  rw [M.setFormula_realize, M.setFormula_realize]
  have hy : ys = j ∘ xs := by
    funext i
    exact ((edges _ _).mp (hs i)).symm
  rw [hy]
  exact j.map_formula phi xs

theorem GraphElementary.graph_exact {M : TransitiveClass.{u}} {graph domain range : M.Element}
    (h : M.GraphElementary graph domain range) (a b : ZFSet.{u}) :
    ZFSet.pair a b ∈ graph.val ↔
      ∃ x : SetDomain domain.val, x.val = a ∧ (h.toEmbedding x).val = b := by
  constructor
  · intro hab
    have hprod := (M.graphBetween_absolute graph domain range).mp h.1.1 hab
    obtain ⟨ha, hb⟩ := ZFSet.pair_mem_prod.mp hprod
    let x : SetDomain domain.val := ⟨a, ha⟩
    let y : SetDomain range.val := ⟨b, hb⟩
    have hedge : M.GraphApplies graph (M.setInclude domain x) (M.setInclude range y) :=
      (M.graphApplies_absolute _ _ _).mpr hab
    exact ⟨x, rfl, congrArg Subtype.val ((h.applies_iff x y).mp hedge)⟩
  · rintro ⟨x, rfl, rfl⟩
    exact (M.graphApplies_absolute _ _ _).mp (h.value_applies x)

private def setFormulaAt {n : Nat} {alpha : Type} (phi : membershipLanguage.Formula (Fin n))
    (xs : Fin n → alpha) (domain : alpha) : membershipLanguage.Formula alpha :=
  (rankPredicateToFormula (setFormula phi)).relabel (Fin.lastCases domain xs)

private theorem setFormulaAt_realize (M : TransitiveClass.{u}) {n : Nat} {alpha : Type}
    (phi : membershipLanguage.Formula (Fin n)) (xs : Fin n → alpha) (domain : alpha)
    (values : alpha → M.Element) :
    (setFormulaAt phi xs domain).Realize values ↔
      M.realize (setFormula phi) (Fin.snoc (values ∘ xs) (values domain)) := by
  rw [setFormulaAt, Formula.realize_relabel, ← M.realize_toFormula]
  have he : values ∘ Fin.lastCases domain xs = Fin.snoc (values ∘ xs) (values domain) := by
    funext i
    cases i using Fin.lastCases with
    | last => simp
    | cast i => simp
  rw [he]

/-- 固定 phi 后，这是真正有限的一阶公式，三个自由参数依次为图、源、靶。 -/
noncomputable def graphPreservesFormula {n : Nat} (phi : membershipLanguage.Formula (Fin n)) :
    membershipLanguage.Formula (Fin 3) :=
  let xs : Fin n → Fin 3 ⊕ (Fin n ⊕ Fin n) := fun i => .inr (.inl i)
  let ys : Fin n → Fin 3 ⊕ (Fin n ⊕ Fin n) := fun i => .inr (.inr i)
  let guard := Formula.iInf (fun i =>
    (rankMemAt (.inl (xs i)) (.inl (.inl 1))) ⊓
    (rankMemAt (.inl (ys i)) (.inl (.inl 2))) ⊓
    (rankGraphAppliesFormula.relabel ![.inl 0, xs i, ys i]))
  (guard.imp ((setFormulaAt phi ys (.inl 2)).iff (setFormulaAt phi xs (.inl 1)))).iAlls (Fin n ⊕ Fin n)

private theorem graphPreservesFormula_realize_outer (M : TransitiveClass.{u})
    {n : Nat} (phi : membershipLanguage.Formula (Fin n)) (graph domain range : M.Element) :
    (graphPreservesFormula phi).Realize ![graph, domain, range] ↔
      ∀ xs ys : Fin n → M.Element,
        (∀ i, (xs i).val ∈ domain.val ∧ (ys i).val ∈ range.val ∧ M.GraphApplies graph (xs i) (ys i)) →
        (M.realize (setFormula phi) (Fin.snoc ys range) ↔
          M.realize (setFormula phi) (Fin.snoc xs domain)) := by
  simp only [graphPreservesFormula, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_iInf, Formula.realize_inf, Formula.realize_iff, setFormulaAt_realize,
    Formula.realize_relabel]
  simp only [Formula.Realize, M.memAt_realize]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  constructor
  · intro h xs ys guards
    have hs := h (Sum.elim xs ys)
    simp only [Sum.elim_inl, Sum.elim_inr] at hs
    apply hs
    intro i
    refine ⟨⟨(guards i).1, (guards i).2.1⟩, ?_⟩
    exact (M.graphAppliesFormula_realize _ _ _).mpr (guards i).2.2
  · intro h tuple guards
    apply h (fun i => tuple (.inl i)) (fun i => tuple (.inr i))
    intro i
    exact ⟨(guards i).1.1, (guards i).1.2,
      (M.graphAppliesFormula_realize _ _ _).mp (guards i).2⟩

theorem graphPreservesFormula_realize (M : TransitiveClass.{u})
    {n : Nat} (phi : membershipLanguage.Formula (Fin n)) (graph domain range : M.Element) :
    (graphPreservesFormula phi).Realize ![graph, domain, range] ↔
      ∀ (xs : Fin n → SetDomain domain.val) (ys : Fin n → SetDomain range.val),
        (∀ i, M.GraphApplies graph (M.setInclude domain (xs i)) (M.setInclude range (ys i))) →
        (M.realize (setFormula phi) (Fin.snoc (M.setInclude range ∘ ys) range) ↔
          M.realize (setFormula phi) (Fin.snoc (M.setInclude domain ∘ xs) domain)) := by
  rw [graphPreservesFormula_realize_outer]
  constructor
  · intro h xs ys edges
    exact h (M.setInclude domain ∘ xs) (M.setInclude range ∘ ys)
      (fun i => ⟨(xs i).property, (ys i).property, edges i⟩)
  · intro h xs ys guards
    let xs' : Fin n → SetDomain domain.val := fun i => ⟨(xs i).val, (guards i).1⟩
    let ys' : Fin n → SetDomain range.val := fun i => ⟨(ys i).val, (guards i).2.1⟩
    have hx : M.setInclude domain ∘ xs' = xs := by funext i; rfl
    have hy : M.setInclude range ∘ ys' = ys := by funext i; rfl
    have hh := h xs' ys' (fun i => (guards i).2.2)
    rwa [hx, hy] at hh

/-- 图初等性等价于真实函数公式和明确生成的有限保持方案。 -/
theorem graphElementary_iff_schema (M : TransitiveClass.{u}) (graph domain range : M.Element) :
    M.GraphElementary graph domain range ↔
      rankFunctionFormula.Realize ![graph, domain, range] ∧
      ∀ (n : Nat) (phi : membershipLanguage.Formula (Fin n)),
        (graphPreservesFormula phi).Realize ![graph, domain, range] := by
  simp only [M.functionFormula_realize, graphPreservesFormula_realize, GraphElementary]

/-- 有限方案能逐公式通过真实模型初等映射输送，因此像图仍有完整初等性。 -/
theorem ElementaryMap.graphElementary_iff {M N : TransitiveClass.{u}} (j : M.ElementaryMap N)
    (graph domain range : M.Element) :
    N.GraphElementary (j graph) (j domain) (j range) ↔ M.GraphElementary graph domain range := by
  rw [N.graphElementary_iff_schema, M.graphElementary_iff_schema]
  have tuple : j ∘ ![graph, domain, range] = ![j graph, j domain, j range] := by
    funext i
    fin_cases i <;> rfl
  constructor
  · rintro ⟨hf, hp⟩
    refine ⟨?_, fun n phi => ?_⟩
    · exact (j.map_formula rankFunctionFormula ![graph, domain, range]).mp (tuple ▸ hf)
    · exact (j.map_formula (graphPreservesFormula phi) ![graph, domain, range]).mp (tuple ▸ hp n phi)
  · rintro ⟨hf, hp⟩
    refine ⟨?_, fun n phi => ?_⟩
    · rw [← tuple]
      exact (j.map_formula rankFunctionFormula ![graph, domain, range]).mpr hf
    · rw [← tuple]
      exact (j.map_formula (graphPreservesFormula phi) ![graph, domain, range]).mpr (hp n phi)

end TransitiveClass
end IBLP
