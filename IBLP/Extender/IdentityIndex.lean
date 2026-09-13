import IBLP.Extender.CommonRefinement

namespace IBLP.Extender.Derivation
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}

theorem identityIndex_exists : ∃ graph : stage.model.Element,
    ZFSet.IsFunc (stage.hierarchy alpha).val (stage.hierarchy alpha).val graph.val ∧
      ∀ x : Seed stage alpha, ZFSet.pair x.val x.val ∈ graph.val := by
  let phi : RankPredicateFormula 0 2 := .equal 0 1
  have sem (x y : stage.model.Element) :
      stage.model.realize phi (Fin.snoc (Fin.snoc ![] x) y) ↔ x = y := Iff.rfl
  obtain ⟨graph, hf, edges⟩ := stage.definableGraph_exists phi ![] (stage.hierarchy alpha)
    (stage.hierarchy alpha) (fun x _ => ⟨x, (sem x x).mpr rfl⟩)
    (fun x y hx h => (sem x y).mp h ▸ hx)
    (fun x y z _ hy hz => ((sem x y).mp hy).symm.trans ((sem x z).mp hz))
  exact ⟨graph, hf, fun x => (edges (stage.rankInclude _ x) (stage.rankInclude _ x)).mpr
    ⟨(stage.mem_hierarchy alpha x.val).mpr x.property, (sem _ _).mpr rfl⟩⟩

noncomputable def identityIndex (ha : Order.IsSuccLimit alpha) : IndexMap stage alpha :=
  IndexMap.ofFunction ha identityIndex_exists.choose identityIndex_exists.choose_spec.1

theorem identityIndex_edge (ha : Order.IsSuccLimit alpha) (x : Seed stage alpha) :
    ZFSet.pair x.val x.val ∈ (identityIndex (stage := stage) ha).graph.val :=
  identityIndex_exists.choose_spec.2 x

theorem indexValue_identity (ha : Order.IsSuccLimit alpha) (x : Seed stage alpha) :
    Representative.indexValue (identityIndex ha) x = x := by
  apply Subtype.ext
  exact ((identityIndex ha).function.2 x.val ((stage.mem_hierarchy alpha x.val).mpr x.property)).unique
    (Representative.indexValue_edge _ x) (identityIndex_edge ha x)

def identityIndexMatrix : RankPredicateFormula 0 2 :=
  .all ((RankPredicateFormula.member 2 0).imp (rankFormulaGraphApplies 1 2 2))

theorem identityIndexMatrix_realize (M : TransitiveClass.{u}) (domain graph : M.Element) :
    M.realize identityIndexMatrix ![domain, graph] ↔
      ∀ x : M.Element, x.val ∈ domain.val → ZFSet.pair x.val x.val ∈ graph.val := by
  change (∀ x, _ → _) ↔ _
  simp only [M.setGraphAtom_realize, TransitiveClass.realize, Fin.snoc]
  rfl

theorem project_identity (D : Derivation stage alpha beta) (ha : Order.IsSuccLimit alpha)
    (seed : Seed stage beta) : D.project (identityIndex ha) seed = seed := by
  have source : (stage.model.rankPart (Order.succ alpha)).realize identityIndexMatrix
      ![top, (identityIndex ha).graph] := by
    apply (identityIndexMatrix_realize _ _ _).mpr
    intro x hx
    exact identityIndex_edge ha ⟨x.val, (stage.mem_hierarchy alpha x.val).mp hx⟩
  have image := (D.map.realize_iff identityIndexMatrix ![top, (identityIndex ha).graph]).mpr source
  have args : D.map ∘ ![top, (identityIndex ha).graph] = ![D.map top, D.map (identityIndex ha).graph] := by
    funext i; fin_cases i <;> rfl
  rw [args, identityIndexMatrix_realize] at image
  let x : Test stage beta := ⟨seed.val, seed.property.1, seed.property.2.trans (Order.lt_succ beta)⟩
  have edge := image x (D.large_top seed)
  exact Subtype.ext (D.project_unique (identityIndex ha) seed seed.val edge).symm

end IBLP.Extender.Derivation
