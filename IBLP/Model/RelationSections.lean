import IBLP.Model.CountableRelation

namespace IBLP
open FullMarkedBLP
universe u

theorem forall_omega_iff (P : ZFSet.{u} → Prop) :
    (∀ i ∈ Ordinal.omega0.toZFSet, P i) ↔ ∀ n : Nat, P (n : Ordinal.{u}).toZFSet := by
  constructor
  · exact fun h n => h _ (natZFSetOmegaEquiv n).property
  · intro h i hi
    obtain ⟨n, hn⟩ := natZFSetOmegaEquiv.surjective ⟨i, hi⟩
    have same := congrArg Subtype.val hn
    change (n : Ordinal.{u}).toZFSet = i at same
    simpa only [same] using h n

def relationSectionMatrix : RankPredicateFormula 0 3 :=
  .all ((RankPredicateFormula.member 3 2).iff (rankFormulaGraphApplies 1 0 3))

theorem relationSectionMatrix_realize (M : TransitiveClass.{u}) (index relation sectionSet : M.Element) :
    M.realize relationSectionMatrix ![index, relation, sectionSet] ↔
      ∀ z, z ∈ sectionSet.val ↔ ZFSet.pair index.val z ∈ relation.val := by
  have sem : M.realize relationSectionMatrix ![index, relation, sectionSet] ↔
      ∀ z : M.Element, z.val ∈ sectionSet.val ↔ ZFSet.pair index.val z.val ∈ relation.val := by
    change (∀ z, M.realize _ (Fin.snoc ![index, relation, sectionSet] z)) ↔ _
    apply forall_congr'
    intro z
    rw [M.pure_iff_realize, M.setGraphAtom_realize]
    rfl
  rw [sem]
  constructor
  · intro h z
    exact ⟨fun hz => (h (M.member sectionSet z hz)).mp hz,
      fun hz => (h ⟨z, (M.pair_components (M.transitive hz relation.property)).2⟩).mpr hz⟩
  · exact fun h z => h z.val

def relationIntersectionPredicate : RankPredicateFormula 0 3 :=
  .all ((RankPredicateFormula.member 3 0).imp (rankFormulaGraphApplies 1 3 2))

theorem relationIntersectionPredicate_realize (M : TransitiveClass.{u}) (indices relation x : M.Element) :
    M.realize relationIntersectionPredicate (Fin.snoc ![indices, relation] x) ↔
      ∀ i ∈ indices.val, ZFSet.pair i x.val ∈ relation.val := by
  have sem : M.realize relationIntersectionPredicate (Fin.snoc ![indices, relation] x) ↔
      ∀ i : M.Element, i.val ∈ indices.val → ZFSet.pair i.val x.val ∈ relation.val := by
    change (∀ i, _ → _) ↔ _
    simp only [M.setGraphAtom_realize, TransitiveClass.realize, Fin.snoc]
    rfl
  rw [sem]
  exact ⟨fun h i hi => h (M.member indices i hi) hi, fun h i hi => h i.val hi⟩

def relationIntersectionMatrix : RankPredicateFormula 0 4 :=
  .all ((RankPredicateFormula.member 4 3).iff ((RankPredicateFormula.member 4 0).and
    (relationIntersectionPredicate.relabelSets ![1, 2, 4])))

theorem relationIntersectionMatrix_realize (M : TransitiveClass.{u})
    (domain indices relation result : M.Element) :
    M.realize relationIntersectionMatrix ![domain, indices, relation, result] ↔
      result.val = ZFSet.sep (fun x => ∀ i ∈ indices.val, ZFSet.pair i x ∈ relation.val) domain.val := by
  have sem : M.realize relationIntersectionMatrix ![domain, indices, relation, result] ↔
      ∀ x : M.Element, x.val ∈ result.val ↔
        x.val ∈ domain.val ∧ ∀ i ∈ indices.val, ZFSet.pair i x.val ∈ relation.val := by
    change (∀ x, M.realize _ (Fin.snoc ![domain, indices, relation, result] x)) ↔ _
    apply forall_congr'
    intro x
    rw [M.pure_iff_realize, M.realize_and, M.realize_relabel]
    have args : Fin.snoc ![domain, indices, relation, result] x ∘ ![1, 2, 4] = Fin.snoc ![indices, relation] x := by
      funext i; fin_cases i <;> rfl
    rw [args, relationIntersectionPredicate_realize]
    rfl
  rw [sem]
  constructor
  · intro h
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_sep]
    exact ⟨fun hx => (h (M.member result x hx)).mp hx,
      fun hx => (h (M.member domain x hx.1)).mpr hx⟩
  · intro h x
    rw [h, ZFSet.mem_sep]

namespace ModelStage

noncomputable def relationIntersection (stage : ModelStage.{u}) (domain indices relation : stage.model.Element) :
    stage.model.Element := stage.separation relationIntersectionPredicate ![indices, relation] domain

theorem relationIntersection_val (stage : ModelStage.{u}) (domain indices relation : stage.model.Element) :
    (stage.relationIntersection domain indices relation).val =
      ZFSet.sep (fun x => ∀ i ∈ indices.val, ZFSet.pair i x ∈ relation.val) domain.val := by
  have sem (x : stage.model.Element) : x.val ∈ (stage.relationIntersection domain indices relation).val ↔
      x.val ∈ domain.val ∧ ∀ i ∈ indices.val, ZFSet.pair i x.val ∈ relation.val := by
    rw [relationIntersection, stage.mem_separation, relationIntersectionPredicate_realize]
  apply ZFSet.ext
  intro x
  rw [ZFSet.mem_sep]
  exact ⟨fun hx => (sem (stage.model.member _ x hx)).mp hx,
    fun hx => (sem (stage.model.member domain x hx.1)).mpr hx⟩

end ModelStage
end IBLP
