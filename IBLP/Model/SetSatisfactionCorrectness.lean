import IBLP.Model.SetCodedAssignment
import IBLP.Model.SetSatisfactionSoundness

namespace IBLP
open FullMarkedBLP
universe u

private theorem table_single {M : TransitiveClass.{u}} (book x : M.Element) :
    SetTableHolds book ![x] ↔ setTuple ![x.val] ∈ book.val := by
  unfold SetTableHolds
  have he : (fun i => (![x] i).val) = ![x.val] := by funext i; fin_cases i; rfl
  rw [he]

private theorem table_pair {M : TransitiveClass.{u}} (book x y : M.Element) :
    SetTableHolds book ![x, y] ↔ setTuple ![x.val, y.val] ∈ book.val := by
  unfold SetTableHolds
  have he : (fun i => (![x, y] i).val) = ![x.val, y.val] := by funext i; fin_cases i <;> rfl
  rw [he]

private theorem table_triple {M : TransitiveClass.{u}} (book x y z : M.Element) :
    SetTableHolds book ![x, y, z] ↔ setTuple ![x.val, y.val, z.val] ∈ book.val := by
  unfold SetTableHolds
  have he : (fun i => (![x, y, z] i).val) = ![x.val, y.val, z.val] := by funext i; fin_cases i <;> rfl
  rw [he]

/-- The actual internally constructed satisfaction set obeys one uniform coded
recursion, including exact support and quantifiers restricted to D. -/
theorem ModelStage.setSatisfaction_coded (stage : ModelStage.{u}) (D : stage.model.Element) :
    SetCodedTruthConditions stage.model stage.syntaxBooks D (stage.setSatisfaction D) := by
  constructor
  · intro p hp
    obtain ⟨n, phi, values, _, he⟩ := (mem_setSatisfaction_iff D.val p.val).mp hp
    exact ⟨stage.ordinal (rankSyntaxCode ⟨n, phi⟩ : Ordinal),
      ⟨setAssignment values, stage.setAssignment_mem D values⟩,
      he, stage.setAssignmentAtCode_formula D phi values⟩
  · intro code assignment valid coded
    rw [table_single] at coded
    obtain ⟨n, hc⟩ := (setFalseTable_iff code.val).mp coded
    obtain ⟨values, ha⟩ := (stage.setAssignmentAtCode_formula_iff D code assignment .falsum hc).mp valid
    rw [hc, ha, stage.setSatisfaction_realize]
    exact id
  · intro code assignment i j x y valid coded hx hy
    rw [table_triple] at coded
    obtain ⟨n, a, b, hc, hi, hj⟩ := (setEqualTable_iff code.val i.val j.val).mp coded
    obtain ⟨values, ha⟩ := (stage.setAssignmentAtCode_formula_iff D code assignment (.equal a b) hc).mp valid
    rw [ha, hi, setAssignment_applies_nat_iff] at hx
    rw [ha, hj, setAssignment_applies_nat_iff] at hy
    rw [hc, ha, stage.setSatisfaction_realize]
    change values a = values b ↔ x = y
    constructor
    · intro he
      exact Subtype.ext (hx.trans ((congrArg Subtype.val he).trans hy.symm))
    · intro he
      exact Subtype.ext (hx.symm.trans ((congrArg Subtype.val he).trans hy))
  · intro code assignment i j x y valid coded hx hy
    rw [table_triple] at coded
    obtain ⟨n, a, b, hc, hi, hj⟩ := (setMemberTable_iff code.val i.val j.val).mp coded
    obtain ⟨values, ha⟩ := (stage.setAssignmentAtCode_formula_iff D code assignment (.member a b) hc).mp valid
    rw [ha, hi, setAssignment_applies_nat_iff] at hx
    rw [ha, hj, setAssignment_applies_nat_iff] at hy
    rw [hc, ha, stage.setSatisfaction_realize, hx, hy]
    rfl
  · intro code assignment p q valid coded
    rw [table_triple] at coded
    obtain ⟨n, left, right, hc, hp, hq⟩ := (setImpTable_iff code.val p.val q.val).mp coded
    obtain ⟨values, ha⟩ := (stage.setAssignmentAtCode_formula_iff D code assignment (.imp left right) hc).mp valid
    rw [hc, ha, hp, hq]
    simp only [stage.setSatisfaction_realize, SetDomain.realize]
  · intro code assignment body arity arityCoded function allCoded
    rw [table_pair] at arityCoded allCoded
    obtain ⟨n, phi, hc, hb⟩ := (setAllTable_iff code.val body.val).mp allCoded
    obtain ⟨m, psi, hcm, hm⟩ := (setArityTable_iff code.val arity.val).mp arityCoded
    have hs := rankSyntaxCode_injective (Nat.cast_injective
      (Ordinal.toZFSet_injective (hc.symm.trans hcm)))
    have hn : n = m := (Sigma.mk.inj hs).1
    subst m
    rw [hm] at function
    obtain ⟨values, ha⟩ := setAssignment_decode function
    rw [hc, ← ha, stage.setSatisfaction_realize]
    change (∀ x : SetDomain D.val, SetDomain.realize D.val phi (Fin.snoc values x)) ↔ _
    constructor
    · intro h x new hx hn
      let xD : SetDomain D.val := ⟨x.val, hx⟩
      have hnew : new.val = setAssignment (Fin.snoc values xD) := by
        rw [setAssignment_snoc]
        simpa only [hm] using hn
      rw [hb, hnew, stage.setSatisfaction_realize]
      exact h xD
    · intro h x
      let new : stage.model.Element := ⟨setAssignment (Fin.snoc values x),
        stage.setAssignment_mem D (Fin.snoc values x)⟩
      have hh := h (stage.model.setInclude D x) new x.property (by
        change setAssignment (Fin.snoc values x) = _
        rw [setAssignment_snoc, hm]
        rfl)
      rw [hb] at hh
      exact (stage.setSatisfaction_realize D phi (Fin.snoc values x)).mp hh

theorem ModelStage.setSatisfaction_formula (stage : ModelStage.{u}) (D : stage.model.Element) :
    setSatisfactionFormula.Realize (Fin.snoc (Fin.snoc stage.syntaxBooks D) (stage.setSatisfaction D)) :=
  (setSatisfactionFormula_realize stage stage.syntaxBooks D (stage.setSatisfaction D)).mpr
    (stage.setSatisfaction_coded D)

/-- One fixed finite formula characterizes the entire actual satisfaction set. -/
theorem ModelStage.setSatisfaction_formula_iff (stage : ModelStage.{u})
    (D truth : stage.model.Element) :
    setSatisfactionFormula.Realize (Fin.snoc (Fin.snoc stage.syntaxBooks D) truth) ↔
      truth.val = IBLP.setSatisfaction D.val := by
  rw [setSatisfactionFormula_realize]
  constructor
  · exact SetCodedTruthConditions.truth_eq
  · intro he
    have same : truth = stage.setSatisfaction D := Subtype.ext he
    rw [same]
    exact stage.setSatisfaction_coded D

theorem ModelStage.setSatisfaction_formula_exists_unique (stage : ModelStage.{u})
    (D : stage.model.Element) :
    ∃! truth : stage.model.Element,
      setSatisfactionFormula.Realize (Fin.snoc (Fin.snoc stage.syntaxBooks D) truth) := by
  refine ⟨stage.setSatisfaction D, stage.setSatisfaction_formula D, ?_⟩
  intro truth ht
  exact Subtype.ext ((stage.setSatisfaction_formula_iff D truth).mp ht)

end IBLP
