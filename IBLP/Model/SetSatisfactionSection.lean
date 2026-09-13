import IBLP.Model.SetSatisfaction
import IBLP.Model.Separation
import IBLP.Model.Graph
import IBLP.Model.FiniteSets

namespace IBLP
open FullMarkedBLP FirstOrder Language
universe u

/-- A finite formula specifying every edge of a finite assignment graph. -/
noncomputable def finiteAssignmentFormula {alpha : Type} {n : Nat}
    (graph : alpha) (indices values : Fin n → alpha) : membershipLanguage.Formula alpha :=
  ((rankMemAt (.inr 0) (.inl graph)).iff
    (BoundedFormula.iSup (fun i =>
      rankOrderedPairAt (.inr 0) (.inl (indices i)) (.inl (values i))))).all

theorem finiteAssignmentFormula_realize (stage : ModelStage.{u}) {alpha : Type} {n : Nat}
    (graph : alpha) (indices values : Fin n → alpha) (args : alpha → stage.model.Element) :
    (finiteAssignmentFormula graph indices values).Realize args ↔
      (args graph).val = ZFSet.range (fun i : Fin n =>
        ZFSet.pair (args (indices i)).val (args (values i)).val) := by
  let M := stage.model
  have semantic : (finiteAssignmentFormula graph indices values).Realize args ↔
      ∀ p : M.Element, p.val ∈ (args graph).val ↔
        ∃ i : Fin n, p.val = ZFSet.pair (args (indices i)).val (args (values i)).val := by
    simp only [finiteAssignmentFormula, Formula.Realize, BoundedFormula.realize_all,
      BoundedFormula.realize_iff, M.memAt_realize, BoundedFormula.realize_iSup,
      M.orderedPairAt_realize, M.orderedPair_absolute, Sum.elim_inl, Sum.elim_inr]
    rfl
  rw [semantic]
  constructor
  · intro h
    apply ZFSet.ext
    intro p
    rw [ZFSet.mem_range]
    constructor
    · intro hp
      obtain ⟨i, hi⟩ := (h (M.member (args graph) p hp)).mp hp
      exact ⟨i, hi.symm⟩
    · rintro ⟨i, rfl⟩
      have pairMem : ZFSet.pair (args (indices i)).val (args (values i)).val ∈ M.carrier := by
        rw [← stage.orderedPair_val (args (indices i)) (args (values i))]
        exact (stage.orderedPair (args (indices i)) (args (values i))).property
      exact (h ⟨_, pairMem⟩).mpr ⟨i, rfl⟩
  · intro he p
    rw [he, ZFSet.mem_range]
    exact exists_congr (fun _ => eq_comm)

/-- The true assignments for one fixed formula, with arbitrary actual index codes. -/
def satisfactionSectionEntry {n : Nat} (phi : RankPredicateFormula 0 n)
    (indices : Fin n → ZFSet.{u}) (code D p : ZFSet.{u}) : Prop :=
  ∃ values : Fin n → SetDomain D,
    SetDomain.realize D phi values ∧
      p = ZFSet.pair code (ZFSet.range (fun i => ZFSet.pair (indices i) (values i).val))

/-- Free parameters: n indices, the formula code, the quantifier domain, the tested pair. -/
noncomputable def satisfactionSectionFormula {n : Nat} (phi : RankPredicateFormula 0 n) :
    membershipLanguage.Formula (Fin (n + 3)) :=
  let xs : Fin n → Fin (n + 3) ⊕ Fin (n + 1) := fun i => .inr i.castSucc
  let index : Fin n → Fin (n + 3) ⊕ Fin (n + 1) := fun i => .inl (i.castAdd 3)
  let code : Fin (n + 3) ⊕ Fin (n + 1) := .inl ((Fin.last n).castAdd 2)
  let domain : Fin (n + 3) ⊕ Fin (n + 1) := .inl ((Fin.last (n + 1)).castSucc)
  let pair : Fin (n + 3) ⊕ Fin (n + 1) := .inl (Fin.last (n + 2))
  let graph : Fin (n + 3) ⊕ Fin (n + 1) := .inr (Fin.last n)
  let guard := Formula.iInf (fun i => rankMemAt (.inl (xs i)) (.inl domain))
  let truth := (rankPredicateToFormula (restrictFormula phi Fin.castSucc (Fin.last n))).relabel
    (Fin.lastCases domain xs)
  ((guard ⊓ truth) ⊓ ((finiteAssignmentFormula graph index xs) ⊓
    rankOrderedPairFormula.relabel ![pair, code, graph])).iExs (Fin (n + 1))

theorem satisfactionSectionFormula_realize (stage : ModelStage.{u}) {n : Nat}
    (phi : RankPredicateFormula 0 n) (indices : Fin n → stage.model.Element)
    (code D p : stage.model.Element) :
    (satisfactionSectionFormula phi).Realize (Fin.snoc (Fin.snoc (Fin.snoc indices code) D) p) ↔
      satisfactionSectionEntry phi (fun i => (indices i).val) code.val D.val p.val := by
  let M := stage.model
  have sem : (satisfactionSectionFormula phi).Realize (Fin.snoc (Fin.snoc (Fin.snoc indices code) D) p) ↔
      ∃ vals : Fin (n + 1) → M.Element,
        ((∀ i : Fin n, (vals i.castSucc).val ∈ D.val) ∧
          M.realize (restrictFormula phi Fin.castSucc (Fin.last n))
              (Fin.snoc (fun i => vals i.castSucc) D)) ∧
        (vals (Fin.last n)).val = ZFSet.range (fun i : Fin n =>
          ZFSet.pair (indices i).val (vals i.castSucc).val) ∧
        p.val = ZFSet.pair code.val (vals (Fin.last n)).val := by
    simp only [satisfactionSectionFormula, Formula.realize_iExs, Formula.realize_inf,
      Formula.realize_iInf,
      finiteAssignmentFormula_realize, Formula.realize_relabel, ← M.realize_toFormula]
    simp only [Formula.Realize, M.memAt_realize]
    simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, Fin.snoc_castAdd,
      Fin.snoc_last, Fin.snoc_castSucc]
    apply exists_congr
    intro vals
    apply and_congr
    · apply and_congr Iff.rfl
      apply iff_of_eq
      congr 1
      funext i
      cases i using Fin.lastCases <;> simp
    have castOne (i : Fin n) : i.castAdd 1 = i.castSucc := rfl
    simp only [castOne, Fin.snoc_castSucc]
    apply and_congr Iff.rfl
    have tuple : (fun x => Sum.elim (Fin.snoc (Fin.snoc (Fin.snoc indices code) D) p) vals
        (![Sum.inl (Fin.last (n + 2)), Sum.inl (Fin.castAdd 2 (Fin.last n)), Sum.inr (Fin.last n)] x)) =
        ![p, code, vals (Fin.last n)] := by
      funext i
      fin_cases i
      · simp
      · have hi : Fin.castAdd 2 (Fin.last n) = (Fin.last n).castSucc.castSucc := rfl
        simp [hi]
      · simp
    rw [tuple]
    exact (M.orderedPairFormula_realize p code (vals (Fin.last n))).trans
      (M.orderedPair_absolute _ _ _)
  rw [sem]
  constructor
  · rintro ⟨vals, ⟨hv, ht⟩, hg, hp⟩
    let values : Fin n → SetDomain D.val := fun i => ⟨(vals i.castSucc).val, hv i⟩
    refine ⟨values, ?_, hp.trans (congrArg (ZFSet.pair code.val) hg)⟩
    exact (M.restrictFormula_realize D phi Fin.castSucc (Fin.last n) values
      (Fin.snoc (fun i => vals i.castSucc) D) (fun _ => by simp; rfl) (by simp)).mp ht
  · rintro ⟨values, ht, hp⟩
    let xs := M.setInclude D ∘ values
    let graph := stage.finiteRange (fun i => stage.orderedPair (indices i) (xs i))
    have hg : graph.val = ZFSet.range (fun i : Fin n => ZFSet.pair (indices i).val (values i).val) := by
      rw [show graph = stage.finiteRange _ from rfl, stage.finiteRange_val]
      congr 1
      funext i
      exact stage.orderedPair_val _ _
    refine ⟨Fin.snoc xs graph, ⟨?_, ?_⟩, ?_, ?_⟩
    · simpa only [Fin.snoc_castSucc] using fun i => (values i).property
    · apply (M.restrictFormula_realize D phi _ _ values _ ?_ ?_).mpr ht
      · intro i
        simp only [Fin.snoc_castSucc]
        rfl
      · simp
    · simpa only [Fin.snoc_last, Fin.snoc_castSucc] using hg
    · simpa only [Fin.snoc_last, hg] using hp

noncomputable def satisfactionSectionSetFormula {n : Nat} (phi : RankPredicateFormula 0 n) :
    RankPredicateFormula 0 (n + 3) :=
  .all ((RankPredicateFormula.member (Fin.last (n + 3)) (Fin.last (n + 2)).castSucc).iff
    (rankPredicateAtom (satisfactionSectionFormula phi)
      (Fin.lastCases (Fin.last (n + 3)) (fun i => i.castAdd 2))))

theorem satisfactionSectionSetFormula_realize (stage : ModelStage.{u}) {n : Nat}
    (phi : RankPredicateFormula 0 n) (indices : Fin n → stage.model.Element)
    (code D result : stage.model.Element) :
    stage.model.realize (satisfactionSectionSetFormula phi)
      (Fin.snoc (Fin.snoc (Fin.snoc indices code) D) result) ↔
      ∀ p : stage.model.Element, p.val ∈ result.val ↔
        satisfactionSectionEntry phi (fun i => (indices i).val) code.val D.val p.val := by
  change (∀ p, stage.model.realize _ _) ↔ _
  apply forall_congr'
  intro p
  simp only [RankPredicateFormula.iff, stage.model.realize_and, TransitiveClass.realize]
  rw [stage.model.realize_atom]
  have tuple : Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc indices code) D) result) p ∘
      Fin.lastCases (Fin.last (n + 3)) (fun i : Fin (n + 2) => i.castAdd 2) =
      Fin.snoc (Fin.snoc (Fin.snoc indices code) D) p := by
    funext i
    cases i using Fin.lastCases with
    | last => simp
    | cast i =>
      have hi : i.castAdd 2 = i.castSucc.castSucc := rfl
      simp only [Function.comp_apply, Fin.lastCases_castSucc, hi, Fin.snoc_castSucc]
  simp only [tuple, Fin.snoc_last, Fin.snoc_castSucc, satisfactionSectionFormula_realize]
  exact iff_def.symm

/-- An actual model set for one fixed finite formula. Existence is transferred
from a genuine set construction, so no external separation principle is assumed. -/
theorem ModelStage.satisfactionSection_exists (stage : ModelStage.{u}) {n : Nat}
    (phi : RankPredicateFormula 0 n) (indices : Fin n → stage.model.Element)
    (code D : stage.model.Element) :
    ∃ result : stage.model.Element, ∀ p : stage.model.Element, p.val ∈ result.val ↔
      satisfactionSectionEntry phi (fun i => (indices i).val) code.val D.val p.val := by
  classical
  have initial : ∀ args, ∃ result, universeClass.{u}.toTransitiveClass.realize
      (satisfactionSectionSetFormula phi) (Fin.snoc args result) := by
    intro args
    let domain := args (Fin.last (n + 1))
    let code := Fin.init args (Fin.last n)
    let indices := Fin.init (Fin.init args)
    letI : Small.{u} (SetDomain domain.val) := ZFSet.small_coe domain.val
    have he : Fin.snoc (Fin.snoc indices code) domain = args := by
      simp only [indices, code, domain, Fin.snoc_init_self]
    let entry (values : Fin n → SetDomain domain.val) : ZFSet.{u} :=
      ZFSet.pair code.val (ZFSet.range (fun i => ZFSet.pair (indices i).val (values i).val))
    let result : universeClass.{u}.toTransitiveClass.Element :=
      ⟨ZFSet.range (fun values : {v : Fin n → SetDomain domain.val //
        SetDomain.realize domain.val phi v} => entry values.val), Set.mem_univ _⟩
    refine ⟨result, ?_⟩
    rw [← he]
    apply (satisfactionSectionSetFormula_realize initialStage phi indices code domain result).mpr
    intro p
    change p.val ∈ ZFSet.range _ ↔ _
    rw [ZFSet.mem_range]
    constructor
    · rintro ⟨v, hv⟩
      exact ⟨v.val, v.property, hv.symm⟩
    · rintro ⟨v, ht, hv⟩
      exact ⟨⟨v, ht⟩, hv.symm⟩
  obtain ⟨result, hr⟩ := stage.transfer_exists (satisfactionSectionSetFormula phi) initial
    (Fin.snoc (Fin.snoc indices code) D)
  exact ⟨result, (satisfactionSectionSetFormula_realize stage phi indices code D result).mp hr⟩

end IBLP



