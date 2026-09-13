import IBLP.Model.Separation
import IBLP.Model.Graph
import FullMarkedBLP.FunctionGraphConstruction

namespace IBLP
open FullMarkedBLP
universe u

/-- Parameters, domain, then universally tested input and existential output. -/
def totalRelationFormula {n : Nat} (phi : RankPredicateFormula 0 (n + 2)) :
    RankPredicateFormula 0 (n + 1) :=
  .all ((RankPredicateFormula.member (Fin.last (n + 1)) (Fin.last n).castSucc).imp
    (phi.relabelSets (Fin.lastCases (Fin.last (n + 2))
      (Fin.lastCases (Fin.last (n + 1)).castSucc (fun i => i.castAdd 3)))).ex)

theorem totalRelationFormula_realize (M : TransitiveClass.{u}) {n : Nat}
    (phi : RankPredicateFormula 0 (n + 2)) (values : Fin n → M.Element) (d : M.Element) :
    M.realize (totalRelationFormula phi) (Fin.snoc values d) ↔
      ∀ x : M.Element, x.val ∈ d.val →
        ∃ y : M.Element, M.realize phi (Fin.snoc (Fin.snoc values x) y) := by
  change (∀ x, _ → _) ↔ _
  apply forall_congr'
  intro x
  apply imp_congr
  · simp [TransitiveClass.realize]
  rw [M.realize_ex]
  apply exists_congr
  intro y
  rw [M.realize_relabel]
  apply iff_of_eq
  apply congrArg (M.realize phi)
  funext i
  cases i using Fin.lastCases with
  | last => simp
  | cast i =>
    cases i using Fin.lastCases with
    | last => simp
    | cast i =>
        simp only [Function.comp_apply, Fin.lastCases_castSucc, Fin.snoc_castSucc, Fin.snoc_castAdd]
        exact Fin.snoc_castSucc (α := fun _ => M.Element) d values i

/-- Parameters, domain, range and graph; every selected graph edge satisfies phi. -/
def choiceGraphMatrix {n : Nat} (phi : RankPredicateFormula 0 (n + 2)) :
    RankPredicateFormula 0 (n + 3) :=
  (rankPredicateAtom rankFunctionFormula
    ![Fin.last (n + 2), (Fin.last n).castSucc.castSucc, (Fin.last (n + 1)).castSucc]).and
    (.all (.all ((rankPredicateAtom rankGraphAppliesFormula
      ![(Fin.last (n + 2)).castSucc.castSucc, (Fin.last (n + 3)).castSucc, Fin.last (n + 4)]).imp
      (phi.relabelSets (Fin.lastCases (Fin.last (n + 4))
        (Fin.lastCases (Fin.last (n + 3)).castSucc (fun i => i.castAdd 5)))))))

theorem choiceGraphMatrix_realize (M : TransitiveClass.{u}) {n : Nat}
    (phi : RankPredicateFormula 0 (n + 2)) (values : Fin n → M.Element) (d r f : M.Element) :
    M.realize (choiceGraphMatrix phi) (Fin.snoc (Fin.snoc (Fin.snoc values d) r) f) ↔
      ZFSet.IsFunc d.val r.val f.val ∧ ∀ x y : M.Element,
        ZFSet.pair x.val y.val ∈ f.val →
          M.realize phi (Fin.snoc (Fin.snoc values x) y) := by
  rw [choiceGraphMatrix, M.realize_and]
  apply and_congr
  · rw [M.realize_atom]
    have tuple : Fin.snoc (Fin.snoc (Fin.snoc values d) r) f ∘
        ![Fin.last (n + 2), (Fin.last n).castSucc.castSucc, (Fin.last (n + 1)).castSucc] =
        ![f, d, r] := by funext i; fin_cases i <;> simp
    rw [tuple, M.functionFormula_realize, M.function_absolute]
  · change (∀ x y, _ → _) ↔ _
    apply forall_congr'
    intro x
    apply forall_congr'
    intro y
    apply imp_congr
    · rw [M.realize_atom]
      have tuple : Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc values d) r) f) x) y ∘
          ![(Fin.last (n + 2)).castSucc.castSucc, (Fin.last (n + 3)).castSucc, Fin.last (n + 4)] =
          ![f, x, y] := by funext i; fin_cases i <;> simp
      rw [tuple, M.graphAppliesFormula_realize, M.graphApplies_absolute]
    · rw [M.realize_relabel]
      apply iff_of_eq
      apply congrArg (M.realize phi)
      funext i
      cases i using Fin.lastCases with
      | last => simp
      | cast i =>
        cases i using Fin.lastCases with
        | last => simp
        | cast i =>
          simp only [Function.comp_apply, Fin.lastCases_castSucc, Fin.snoc_castSucc, Fin.snoc_castAdd]
          exact Fin.snoc_castSucc (α := fun _ => M.Element) d values i

/-- A finite first-order choice instance, with no external predicate closure assumption. -/
theorem ModelStage.choiceGraph_exists (stage : ModelStage.{u}) {n : Nat}
    (phi : RankPredicateFormula 0 (n + 2)) (values : Fin n → stage.model.Element)
    (d : stage.model.Element)
    (total : ∀ x : stage.model.Element, x.val ∈ d.val →
      ∃ y : stage.model.Element, stage.model.realize phi (Fin.snoc (Fin.snoc values x) y)) :
    ∃ r f : stage.model.Element, ZFSet.IsFunc d.val r.val f.val ∧
      ∀ x y : stage.model.Element, ZFSet.pair x.val y.val ∈ f.val →
        stage.model.realize phi (Fin.snoc (Fin.snoc values x) y) := by
  classical
  let sentence := (totalRelationFormula phi).imp (choiceGraphMatrix phi).ex.ex
  have initial : ∀ args, universeClass.{u}.toTransitiveClass.realize sentence args := by
    intro args
    let params := Fin.init args
    let domain := args (Fin.last n)
    have args_eq : Fin.snoc params domain = args := Fin.snoc_init_self args
    rw [← args_eq]
    change universeClass.toTransitiveClass.realize (totalRelationFormula phi) _ → _
    intro h
    have ht := (totalRelationFormula_realize _ _ params domain).mp h
    let witness (a : domain.val) : universeClass.{u}.toTransitiveClass.Element :=
      (ht ⟨a.val, Set.mem_univ _⟩ a.property).choose
    let range : ZFSet.{u} := ZFSet.range (fun a : domain.val => (witness a).val)
    let funValue (a : domain.val) : range := ⟨(witness a).val, ZFSet.mem_range_self a⟩
    let graph := zfFunctionGraph funValue
    rw [universeClass.toTransitiveClass.realize_ex]
    refine ⟨⟨range, Set.mem_univ _⟩, ?_⟩
    rw [universeClass.toTransitiveClass.realize_ex]
    refine ⟨⟨graph, Set.mem_univ _⟩, (choiceGraphMatrix_realize _ _ _ _ _ _).mpr ?_⟩
    refine ⟨zfFunctionGraph_isFunc funValue, ?_⟩
    intro x y hxy
    obtain ⟨hx, he⟩ := (mem_zfFunctionGraph funValue x.val y.val).mp hxy
    have eqx : (⟨x.val, Set.mem_univ _⟩ : universeClass.{u}.toTransitiveClass.Element) = x :=
      Subtype.ext rfl
    have eqy : witness ⟨x.val, hx⟩ = y := Subtype.ext he
    have hw := (ht ⟨x.val, Set.mem_univ _⟩ hx).choose_spec
    change universeClass.toTransitiveClass.realize phi
      (Fin.snoc (Fin.snoc params ⟨x.val, Set.mem_univ _⟩) (witness ⟨x.val, hx⟩)) at hw
    simpa only [eqx, eqy] using hw
  have transferred := stage.transfer_schema sentence initial (Fin.snoc values d)
  have ht := (totalRelationFormula_realize _ _ _ _).mpr total
  have h := transferred ht
  rw [stage.model.realize_ex] at h
  obtain ⟨r, hr⟩ := h
  rw [stage.model.realize_ex] at hr
  obtain ⟨f, hf⟩ := hr
  exact ⟨r, f, (choiceGraphMatrix_realize _ _ _ _ _ _).mp hf⟩

/-- Collection witnesses are elements of an actual set belonging to the model. -/
theorem ModelStage.collection_exists (stage : ModelStage.{u}) {n : Nat}
    (phi : RankPredicateFormula 0 (n + 2)) (values : Fin n → stage.model.Element)
    (d : stage.model.Element)
    (total : ∀ x : stage.model.Element, x.val ∈ d.val →
      ∃ y : stage.model.Element, stage.model.realize phi (Fin.snoc (Fin.snoc values x) y)) :
    ∃ r : stage.model.Element, ∀ x : stage.model.Element, x.val ∈ d.val →
      ∃ y : stage.model.Element, y.val ∈ r.val ∧
        stage.model.realize phi (Fin.snoc (Fin.snoc values x) y) := by
  obtain ⟨r, f, hf, hphi⟩ := stage.choiceGraph_exists phi values d total
  refine ⟨r, ?_⟩
  intro x hx
  obtain ⟨y, hy, _⟩ := hf.2 x.val hx
  have hyr := (ZFSet.pair_mem_prod.mp (hf.1 hy)).2
  exact ⟨stage.model.member r y hyr, hyr, hphi x (stage.model.member r y hyr) hy⟩

/-- The image predicate, with parameters followed by domain and tested output. -/
def relationImageFormula {n : Nat} (phi : RankPredicateFormula 0 (n + 2)) :
    RankPredicateFormula 0 (n + 2) :=
  ((RankPredicateFormula.member (Fin.last (n + 2)) (Fin.last n).castSucc.castSucc).and
    (phi.relabelSets (Fin.lastCases (Fin.last (n + 1)).castSucc
      (Fin.lastCases (Fin.last (n + 2)) (fun i => i.castAdd 3))))).ex

theorem relationImageFormula_realize (M : TransitiveClass.{u}) {n : Nat}
    (phi : RankPredicateFormula 0 (n + 2)) (values : Fin n → M.Element) (d y : M.Element) :
    M.realize (relationImageFormula phi) (Fin.snoc (Fin.snoc values d) y) ↔
      ∃ x : M.Element, x.val ∈ d.val ∧
        M.realize phi (Fin.snoc (Fin.snoc values x) y) := by
  rw [relationImageFormula, M.realize_ex]
  apply exists_congr
  intro x
  rw [M.realize_and]
  apply and_congr
  · simp [TransitiveClass.realize]
  · rw [M.realize_relabel]
    apply iff_of_eq
    apply congrArg (M.realize phi)
    funext i
    cases i using Fin.lastCases with
    | last => simp
    | cast i =>
      cases i using Fin.lastCases with
      | last => simp
      | cast i =>
        simp only [Function.comp_apply, Fin.lastCases_castSucc, Fin.snoc_castSucc, Fin.snoc_castAdd]
        exact Fin.snoc_castSucc (α := fun _ => M.Element) d values i

/-- Strong collection discards irrelevant members of the bound supplied by collection. -/
theorem ModelStage.strong_collection_exists (stage : ModelStage.{u}) {n : Nat}
    (phi : RankPredicateFormula 0 (n + 2)) (values : Fin n → stage.model.Element)
    (d : stage.model.Element)
    (total : ∀ x : stage.model.Element, x.val ∈ d.val →
      ∃ y : stage.model.Element, stage.model.realize phi (Fin.snoc (Fin.snoc values x) y)) :
    ∃ r : stage.model.Element,
      (∀ x : stage.model.Element, x.val ∈ d.val → ∃ y : stage.model.Element,
        y.val ∈ r.val ∧ stage.model.realize phi (Fin.snoc (Fin.snoc values x) y)) ∧
      ∀ y : stage.model.Element, y.val ∈ r.val → ∃ x : stage.model.Element,
        x.val ∈ d.val ∧ stage.model.realize phi (Fin.snoc (Fin.snoc values x) y) := by
  obtain ⟨r, hr⟩ := stage.collection_exists phi values d total
  let result := stage.separation (relationImageFormula phi) (Fin.snoc values d) r
  have membership (y : stage.model.Element) : y.val ∈ result.val ↔ y.val ∈ r.val ∧
      ∃ x : stage.model.Element, x.val ∈ d.val ∧
        stage.model.realize phi (Fin.snoc (Fin.snoc values x) y) := by
    rw [stage.mem_separation, relationImageFormula_realize]
  refine ⟨result, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, hphi⟩ := hr x hx
    exact ⟨y, (membership y).mpr ⟨hy, x, hx, hphi⟩, hphi⟩
  · intro y hy
    exact ((membership y).mp hy).2

/-- Replacement for each finite first-order formula, with exact internal image membership. -/
theorem ModelStage.replacement_exists (stage : ModelStage.{u}) {n : Nat}
    (phi : RankPredicateFormula 0 (n + 2)) (values : Fin n → stage.model.Element)
    (d : stage.model.Element)
    (functional : ∀ x : stage.model.Element, x.val ∈ d.val →
      ∃! y : stage.model.Element, stage.model.realize phi (Fin.snoc (Fin.snoc values x) y)) :
    ∃ r : stage.model.Element, ∀ y : stage.model.Element,
      y.val ∈ r.val ↔ ∃ x : stage.model.Element, x.val ∈ d.val ∧
        stage.model.realize phi (Fin.snoc (Fin.snoc values x) y) := by
  obtain ⟨r, forward, backward⟩ := stage.strong_collection_exists phi values d
    (fun x hx => (functional x hx).exists)
  refine ⟨r, fun y => ⟨backward y, ?_⟩⟩
  rintro ⟨x, hx, hxy⟩
  obtain ⟨z, hz, hxz⟩ := forward x hx
  have same : y = z := (functional x hx).unique hxy hxz
  simpa only [same] using hz

noncomputable def ModelStage.replacement (stage : ModelStage.{u}) {n : Nat}
    (phi : RankPredicateFormula 0 (n + 2)) (values : Fin n → stage.model.Element)
    (d : stage.model.Element)
    (functional : ∀ x : stage.model.Element, x.val ∈ d.val →
      ∃! y : stage.model.Element, stage.model.realize phi (Fin.snoc (Fin.snoc values x) y)) :
    stage.model.Element := (stage.replacement_exists phi values d functional).choose

theorem ModelStage.mem_replacement (stage : ModelStage.{u}) {n : Nat}
    (phi : RankPredicateFormula 0 (n + 2)) (values : Fin n → stage.model.Element)
    (d : stage.model.Element)
    (functional : ∀ x : stage.model.Element, x.val ∈ d.val →
      ∃! y : stage.model.Element, stage.model.realize phi (Fin.snoc (Fin.snoc values x) y))
    (y : stage.model.Element) :
    y.val ∈ (stage.replacement phi values d functional).val ↔
      ∃ x : stage.model.Element, x.val ∈ d.val ∧
        stage.model.realize phi (Fin.snoc (Fin.snoc values x) y) :=
  (stage.replacement_exists phi values d functional).choose_spec y

/-- The chosen witness is represented by a set graph in M, rather than merely by an
external function on M's elements. The formula still quantifies only over M. -/
structure FormulaChoiceFunction (M : TransitiveClass.{u}) {n : Nat}
    (phi : RankPredicateFormula 0 (n + 2)) (values : Fin n → M.Element) (d : M.Element) where
  range : M.Element
  graph : M.Element
  isFunction : ZFSet.IsFunc d.val range.val graph.val
  satisfies : ∀ x y : M.Element, ZFSet.pair x.val y.val ∈ graph.val →
    M.realize phi (Fin.snoc (Fin.snoc values x) y)

noncomputable def ModelStage.choiceFunction (stage : ModelStage.{u}) {n : Nat}
    (phi : RankPredicateFormula 0 (n + 2)) (values : Fin n → stage.model.Element)
    (d : stage.model.Element)
    (total : ∀ x : stage.model.Element, x.val ∈ d.val →
      ∃ y : stage.model.Element, stage.model.realize phi (Fin.snoc (Fin.snoc values x) y)) :
    FormulaChoiceFunction stage.model phi values d :=
  let h := stage.choiceGraph_exists phi values d total
  { range := h.choose
    graph := h.choose_spec.choose
    isFunction := h.choose_spec.choose_spec.1
    satisfies := h.choose_spec.choose_spec.2 }

namespace FormulaChoiceFunction

variable {M : TransitiveClass.{u}} {n : Nat} {phi : RankPredicateFormula 0 (n + 2)}
  {values : Fin n → M.Element} {d : M.Element} (f : FormulaChoiceFunction M phi values d)

theorem value_exists (x : M.Element) (hx : x.val ∈ d.val) :
    ∃ y : M.Element, y.val ∈ f.range.val ∧ ZFSet.pair x.val y.val ∈ f.graph.val := by
  obtain ⟨y, hy, _⟩ := f.isFunction.2 x.val hx
  have hyr := (ZFSet.pair_mem_prod.mp (f.isFunction.1 hy)).2
  exact ⟨M.member f.range y hyr, hyr, hy⟩

noncomputable def value (x : M.Element) (hx : x.val ∈ d.val) : M.Element :=
  (f.value_exists x hx).choose

theorem value_mem_range (x : M.Element) (hx : x.val ∈ d.val) :
    (f.value x hx).val ∈ f.range.val := (f.value_exists x hx).choose_spec.1

theorem value_graph (x : M.Element) (hx : x.val ∈ d.val) :
    ZFSet.pair x.val (f.value x hx).val ∈ f.graph.val := (f.value_exists x hx).choose_spec.2

theorem value_realizes (x : M.Element) (hx : x.val ∈ d.val) :
    M.realize phi (Fin.snoc (Fin.snoc values x) (f.value x hx)) :=
  f.satisfies x (f.value x hx) (f.value_graph x hx)

theorem graph_iff_value (x y : M.Element) (hx : x.val ∈ d.val) :
    ZFSet.pair x.val y.val ∈ f.graph.val ↔ y = f.value x hx := by
  constructor
  · intro hxy
    exact Subtype.ext ((f.isFunction.2 x.val hx).unique hxy (f.value_graph x hx))
  · rintro rfl
    exact f.value_graph x hx

end FormulaChoiceFunction

end IBLP
