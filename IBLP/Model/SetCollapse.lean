import IBLP.Model.SetCollapseFormula

namespace IBLP
open FullMarkedBLP
universe u

/-- An actual internal graph satisfying the full recursive collapse
equation. Existence is proved below from external well-foundedness. -/
structure InternalSetCollapse (stage : ModelStage.{u}) (domain relation : stage.model.Element) where
  range : stage.model.Element
  graph : stage.model.Element
  function : ZFSet.IsFunc domain.val range.val graph.val
  recursion : stage.model.realize collapseRecursionMatrix ![domain, relation, graph]

theorem ModelStage.setCollapse_exists (stage : ModelStage.{u}) (domain relation : stage.model.Element)
    (wf : WellFounded (setRelation domain.val relation.val)) : Nonempty (InternalSetCollapse stage domain relation) := by
  let phi := setWellFoundedMatrix.imp collapseGraphMatrix.ex.ex
  have initialPair (d r : universeClass.{u}.toTransitiveClass.Element) :
      universeClass.toTransitiveClass.realize phi ![d, r] := by
    intro h
    obtain ⟨range, graph, hgraph⟩ := universe_collapseGraph_exists d r ((universe_setWellFounded_iff d r).mp h)
    rw [universeClass.toTransitiveClass.realize_ex]
    refine ⟨range, ?_⟩
    rw [universeClass.toTransitiveClass.realize_ex]
    refine ⟨graph, ?_⟩
    have args : Fin.snoc (Fin.snoc ![d, r] range) graph = ![d, r, range, graph] := by
      funext i; fin_cases i <;> rfl
    rwa [args]
  have initial : ∀ values, universeClass.{u}.toTransitiveClass.realize phi values := by
    intro values
    have args : ![values 0, values 1] = values := by funext i; fin_cases i <;> rfl
    simpa only [args] using initialPair (values 0) (values 1)
  have transferred := stage.transfer_schema phi initial ![domain, relation]
  have h := transferred (setWellFounded_of_external stage.model domain relation wf)
  rw [stage.model.realize_ex] at h
  obtain ⟨range, h⟩ := h
  rw [stage.model.realize_ex] at h
  obtain ⟨graph, h⟩ := h
  have args : Fin.snoc (Fin.snoc ![domain, relation] range) graph = ![domain, relation, range, graph] := by
    funext i; fin_cases i <;> rfl
  rw [args, collapseGraphMatrix_realize] at h
  exact ⟨⟨range, graph, h.1, h.2⟩⟩

noncomputable def ModelStage.setCollapse (stage : ModelStage.{u}) (domain relation : stage.model.Element)
    (wf : WellFounded (setRelation domain.val relation.val)) : InternalSetCollapse stage domain relation :=
  Classical.choice (stage.setCollapse_exists domain relation wf)

namespace InternalSetCollapse
variable {stage : ModelStage.{u}} {domain relation : stage.model.Element}

noncomputable def value (C : InternalSetCollapse stage domain relation) (x : SetDomain domain.val) :
    stage.model.Element :=
  let y := zfGraphFunction C.function x
  stage.model.member C.range y.val y.property

theorem value_edge (C : InternalSetCollapse stage domain relation) (x : SetDomain domain.val) :
    ZFSet.pair x.val (C.value x).val ∈ C.graph.val := zfGraphFunction_edge C.function x

theorem value_unique (C : InternalSetCollapse stage domain relation) (x : SetDomain domain.val)
    (y : ZFSet.{u}) (edge : ZFSet.pair x.val y ∈ C.graph.val) : y = (C.value x).val :=
  (C.function.2 x.val x.property).unique edge (C.value_edge x)

theorem mem_value (C : InternalSetCollapse stage domain relation) (x : SetDomain domain.val) (z : ZFSet.{u}) :
    z ∈ (C.value x).val ↔ ∃ p : SetDomain domain.val,
      setRelation domain.val relation.val p x ∧ (C.value p).val = z := by
  have sem := (collapseRecursionMatrix_realize _ _ _ _).mp C.recursion
    (stage.model.member domain x.val x.property) (C.value x) x.property (C.value_edge x)
  constructor
  · intro hz
    obtain ⟨p, hp, edge, valueEdge⟩ := (sem (stage.model.member (C.value x) z hz)).mp hz
    exact ⟨⟨p.val, hp⟩, edge, (C.value_unique ⟨p.val, hp⟩ z valueEdge).symm⟩
  · rintro ⟨p, edge, valueEq⟩
    rw [← valueEq]
    exact (sem (C.value p)).mpr
      ⟨stage.model.member domain p.val p.property, p.property, edge, C.value_edge p⟩

theorem value_eq_collapse (C : InternalSetCollapse stage domain relation)
    (wf : WellFounded (setRelation domain.val relation.val)) (x : SetDomain domain.val) :
    (C.value x).val = Extender.collapse.{u, u+1} (setRelation domain.val relation.val) wf x := by
  have eqFunctions := Extender.collapse_unique.{u, u+1} (setRelation domain.val relation.val) wf
    (fun p => (C.value p).val) C.mem_value
  exact congrFun eqFunctions x

end InternalSetCollapse
end IBLP
