import IBLP.Model.DefinableGraph
import IBLP.Model.BoundedGraph

namespace IBLP
open FullMarkedBLP FirstOrder Language
universe u

theorem TransitiveClass.graphFormulaAtom_realize (M : TransitiveClass.{u}) {n : Nat}
    (f x y : Fin n) (values : Fin n → M.Element) :
    M.realize (rankPredicateAtom rankGraphAppliesFormula ![f, x, y]) values ↔
      ZFSet.pair (values x).val (values y).val ∈ (values f).val := by
  rw [M.realize_atom]
  have tuple : values ∘ ![f, x, y] = ![values f, values x, values y] := by
    funext i; fin_cases i <;> rfl
  rw [tuple, M.graphAppliesFormula_realize, M.graphApplies_absolute]

def graphCompRelation : RankPredicateFormula 0 4 :=
  ((rankPredicateAtom rankGraphAppliesFormula ![0, 2, 4]).and
    (rankPredicateAtom rankGraphAppliesFormula ![1, 4, 3])).ex

theorem graphCompRelation_realize (M : TransitiveClass.{u}) (f g x z : M.Element) :
    M.realize graphCompRelation (Fin.snoc (Fin.snoc ![f, g] x) z) ↔
      ∃ y : M.Element, ZFSet.pair x.val y.val ∈ f.val ∧ ZFSet.pair y.val z.val ∈ g.val := by
  simp [graphCompRelation, M.realize_ex, M.realize_and, M.graphFormulaAtom_realize]

namespace ModelStage

section Composition
variable (stage : ModelStage.{u}) (f g domain middle source range : stage.model.Element)
  (hf : ZFSet.IsFunc domain.val middle.val f.val)
  (hg : ZFSet.IsFunc source.val range.val g.val) (included : middle.val ⊆ source.val)
include stage f g domain middle source range hf hg included

theorem compGraph_exists : ∃ graph : stage.model.Element,
    ZFSet.IsFunc domain.val range.val graph.val ∧ ∀ x z : ZFSet.{u},
      ZFSet.pair x z ∈ graph.val ↔ ∃ y : ZFSet.{u}, ZFSet.pair x y ∈ f.val ∧ ZFSet.pair y z ∈ g.val := by
  have total (x : stage.model.Element) (hx : x.val ∈ domain.val) :
      ∃ z : stage.model.Element, stage.model.realize graphCompRelation (Fin.snoc (Fin.snoc ![f, g] x) z) := by
    obtain ⟨y, hy, _⟩ := hf.2 x.val hx
    have ym := (ZFSet.pair_mem_prod.mp (hf.1 hy)).2
    obtain ⟨z, hz, _⟩ := hg.2 y (included ym)
    have zr := (ZFSet.pair_mem_prod.mp (hg.1 hz)).2
    refine ⟨stage.model.member range z zr, (graphCompRelation_realize _ _ _ _ _).mpr ?_⟩
    exact ⟨stage.model.member middle y ym, hy, hz⟩
  have bounded (x z : stage.model.Element) (_ : x.val ∈ domain.val)
      (h : stage.model.realize graphCompRelation (Fin.snoc (Fin.snoc ![f, g] x) z)) : z.val ∈ range.val := by
    obtain ⟨_, _, hz⟩ := (graphCompRelation_realize _ _ _ _ _).mp h
    exact (ZFSet.pair_mem_prod.mp (hg.1 hz)).2
  have unique (x z z' : stage.model.Element) (hx : x.val ∈ domain.val)
      (h : stage.model.realize graphCompRelation (Fin.snoc (Fin.snoc ![f, g] x) z))
      (h' : stage.model.realize graphCompRelation (Fin.snoc (Fin.snoc ![f, g] x) z')) : z = z' := by
    obtain ⟨y, hxy, hyz⟩ := (graphCompRelation_realize _ _ _ _ _).mp h
    obtain ⟨y', hxy', hyz'⟩ := (graphCompRelation_realize _ _ _ _ _).mp h'
    have same : y = y' := Subtype.ext ((hf.2 x.val hx).unique hxy hxy')
    subst y'
    have ys := included (ZFSet.pair_mem_prod.mp (hf.1 hxy)).2
    exact Subtype.ext ((hg.2 y.val ys).unique hyz hyz')
  obtain ⟨graph, function, edges⟩ :=
    stage.definableGraph_exists graphCompRelation ![f, g] domain range total bounded unique
  refine ⟨graph, function, ?_⟩
  intro x z
  constructor
  · intro edge
    obtain ⟨hx, hz⟩ := ZFSet.pair_mem_prod.mp (function.1 edge)
    have rel := ((edges (stage.model.member domain x hx) (stage.model.member range z hz)).mp edge).2
    obtain ⟨y, hxy, hyz⟩ := (graphCompRelation_realize _ _ _ _ _).mp rel
    exact ⟨y.val, hxy, hyz⟩
  · rintro ⟨y, hxy, hyz⟩
    obtain ⟨hx, hy⟩ := ZFSet.pair_mem_prod.mp (hf.1 hxy)
    have hz := (ZFSet.pair_mem_prod.mp (hg.1 hyz)).2
    apply (edges (stage.model.member domain x hx) (stage.model.member range z hz)).mpr
    exact ⟨hx, (graphCompRelation_realize _ _ _ _ _).mpr ⟨stage.model.member middle y hy, hxy, hyz⟩⟩

noncomputable def compGraph : stage.model.Element :=
  (stage.compGraph_exists f g domain middle source range hf hg included).choose

theorem compGraph_function : ZFSet.IsFunc domain.val range.val
    (stage.compGraph f g domain middle source range hf hg included).val :=
  (stage.compGraph_exists f g domain middle source range hf hg included).choose_spec.1

theorem compGraph_edge_iff (x z : ZFSet.{u}) :
    ZFSet.pair x z ∈ (stage.compGraph f g domain middle source range hf hg included).val ↔
      ∃ y : ZFSet.{u}, ZFSet.pair x y ∈ f.val ∧ ZFSet.pair y z ∈ g.val :=
  (stage.compGraph_exists f g domain middle source range hf hg included).choose_spec.2 x z

end Composition

section Restriction
variable (stage : ModelStage.{u}) (f domain range smaller : stage.model.Element)
  (hf : ZFSet.IsFunc domain.val range.val f.val) (included : smaller.val ⊆ domain.val)
include stage f domain range smaller hf included

theorem restrictGraph_exists : ∃ graph : stage.model.Element,
    ZFSet.IsFunc smaller.val range.val graph.val ∧ ∀ x y : ZFSet.{u},
      ZFSet.pair x y ∈ graph.val ↔ x ∈ smaller.val ∧ ZFSet.pair x y ∈ f.val := by
  let phi : RankPredicateFormula 0 3 := rankPredicateAtom rankGraphAppliesFormula ![0, 1, 2]
  have semantic (x y : stage.model.Element) :
      stage.model.realize phi (Fin.snoc (Fin.snoc ![f] x) y) ↔ ZFSet.pair x.val y.val ∈ f.val := by
    simp [phi, stage.model.graphFormulaAtom_realize]
  have total (x : stage.model.Element) (hx : x.val ∈ smaller.val) :
      ∃ y : stage.model.Element, stage.model.realize phi (Fin.snoc (Fin.snoc ![f] x) y) := by
    obtain ⟨y, hy, _⟩ := hf.2 x.val (included hx)
    have hyr := (ZFSet.pair_mem_prod.mp (hf.1 hy)).2
    exact ⟨stage.model.member range y hyr, (semantic _ _).mpr hy⟩
  have bounded (x y : stage.model.Element) (_ : x.val ∈ smaller.val)
      (h : stage.model.realize phi (Fin.snoc (Fin.snoc ![f] x) y)) : y.val ∈ range.val :=
    (ZFSet.pair_mem_prod.mp (hf.1 ((semantic _ _).mp h))).2
  have unique (x y z : stage.model.Element) (hx : x.val ∈ smaller.val)
      (h : stage.model.realize phi (Fin.snoc (Fin.snoc ![f] x) y))
      (h' : stage.model.realize phi (Fin.snoc (Fin.snoc ![f] x) z)) : y = z :=
    Subtype.ext ((hf.2 x.val (included hx)).unique ((semantic _ _).mp h) ((semantic _ _).mp h'))
  obtain ⟨graph, function, edges⟩ := stage.definableGraph_exists phi ![f] smaller range total bounded unique
  refine ⟨graph, function, ?_⟩
  intro x y
  constructor
  · intro edge
    obtain ⟨hx, hy⟩ := ZFSet.pair_mem_prod.mp (function.1 edge)
    have rel := ((edges (stage.model.member smaller x hx) (stage.model.member range y hy)).mp edge).2
    exact ⟨hx, (semantic _ _).mp rel⟩
  · rintro ⟨hx, edge⟩
    have hy := (ZFSet.pair_mem_prod.mp (hf.1 edge)).2
    exact (edges (stage.model.member smaller x hx) (stage.model.member range y hy)).mpr
      ⟨hx, (semantic _ _).mpr edge⟩

noncomputable def restrictGraph : stage.model.Element :=
  (stage.restrictGraph_exists f domain range smaller hf included).choose

theorem restrictGraph_function : ZFSet.IsFunc smaller.val range.val
    (stage.restrictGraph f domain range smaller hf included).val :=
  (stage.restrictGraph_exists f domain range smaller hf included).choose_spec.1

theorem restrictGraph_edge_iff (x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ (stage.restrictGraph f domain range smaller hf included).val ↔
      x ∈ smaller.val ∧ ZFSet.pair x y ∈ f.val :=
  (stage.restrictGraph_exists f domain range smaller hf included).choose_spec.2 x y

end Restriction
end ModelStage
end IBLP
