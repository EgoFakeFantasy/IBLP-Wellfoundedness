import IBLP.Model.SetSatisfactionSection
import IBLP.Model.CountableUnion

namespace IBLP
open FullMarkedBLP
universe u

theorem ModelStage.setAssignment_mem (stage : ModelStage.{u}) (D : stage.model.Element)
    {n : Nat} (values : Fin n → SetDomain D.val) :
    setAssignment values ∈ stage.model.carrier := by
  have he : setAssignment values =
      (stage.finiteGraph (stage.model.setInclude D ∘ values)).val := by
    rw [stage.finiteGraph_val]
    rfl
  rw [he]
  exact (stage.finiteGraph _).property

noncomputable def ModelStage.satisfactionSection (stage : ModelStage.{u})
    (D : stage.model.Element) {n : Nat} (phi : RankPredicateFormula 0 n) : stage.model.Element :=
  (stage.satisfactionSection_exists phi (fun i => stage.ordinal (i.val : Ordinal))
    (stage.ordinal (rankSyntaxCode ⟨n, phi⟩ : Ordinal)) D).choose

theorem ModelStage.mem_satisfactionSection (stage : ModelStage.{u})
    (D : stage.model.Element) {n : Nat} (phi : RankPredicateFormula 0 n) (p : ZFSet.{u}) :
    p ∈ (stage.satisfactionSection D phi).val ↔
      ∃ values : Fin n → SetDomain D.val, SetDomain.realize D.val phi values ∧
        p = ZFSet.pair (rankSyntaxCode ⟨n, phi⟩ : Ordinal).toZFSet (setAssignment values) := by
  have spec := (stage.satisfactionSection_exists phi (fun i => stage.ordinal (i.val : Ordinal))
    (stage.ordinal (rankSyntaxCode ⟨n, phi⟩ : Ordinal)) D).choose_spec
  constructor
  · intro hp
    exact (spec (stage.model.member (stage.satisfactionSection D phi) p hp)).mp hp
  · rintro ⟨values, ht, rfl⟩
    let assignment : stage.model.Element := ⟨setAssignment values, stage.setAssignment_mem D values⟩
    let pair := stage.orderedPair (stage.ordinal (rankSyntaxCode ⟨n, phi⟩ : Ordinal)) assignment
    have hp : pair.val = ZFSet.pair (rankSyntaxCode ⟨n, phi⟩ : Ordinal).toZFSet
        (setAssignment values) := stage.orderedPair_val _ _
    have hw := (spec pair).mpr ⟨values, ht, hp⟩
    rwa [hp] at hw

theorem mem_setSatisfaction_iff (D p : ZFSet.{u}) : p ∈ setSatisfaction D ↔
    ∃ (n : Nat) (phi : RankPredicateFormula 0 n) (values : Fin n → SetDomain D),
      SetDomain.realize D phi values ∧
        p = ZFSet.pair (rankSyntaxCode ⟨n, phi⟩ : Ordinal).toZFSet (setAssignment values) := by
  rw [setSatisfaction, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, n, phi, values, hp, ht⟩
    exact ⟨n, phi, values, ht, hp⟩
  · rintro ⟨n, phi, values, ht, rfl⟩
    refine ⟨ZFSet.pair_mem_prod.mpr ⟨?_, ?_⟩, n, phi, values, rfl, ht⟩
    · exact Ordinal.toZFSet_mem_toZFSet_iff.mpr (Ordinal.natCast_lt_omega0 _)
    · exact ZFSet.mem_powerset.mpr (setAssignment_subset values)

noncomputable def setSyntaxEnumerate (n : Nat) : RankPureSyntax := by
  letI : Nonempty RankPureSyntax := ⟨⟨0, .falsum⟩⟩
  exact Function.invFun rankSyntaxCode n

theorem setSyntaxEnumerate_code (phi : RankPureSyntax) :
    setSyntaxEnumerate (rankSyntaxCode phi) = phi := by
  letI : Nonempty RankPureSyntax := ⟨⟨0, .falsum⟩⟩
  unfold setSyntaxEnumerate
  exact Function.leftInverse_invFun rankSyntaxCode_injective phi

theorem ModelStage.mem_satisfactionSections_iff (stage : ModelStage.{u})
    (D : stage.model.Element) (p : ZFSet.{u}) :
    (∃ n : Nat, p ∈ (stage.satisfactionSection D (setSyntaxEnumerate n).2).val) ↔
      p ∈ setSatisfaction D.val := by
  simp only [stage.mem_satisfactionSection, mem_setSatisfaction_iff]
  constructor
  · rintro ⟨n, values, ht, hp⟩
    exact ⟨(setSyntaxEnumerate n).1, (setSyntaxEnumerate n).2, values, ht, hp⟩
  · rintro ⟨n, phi, values, ht, hp⟩
    refine ⟨rankSyntaxCode ⟨n, phi⟩, ?_⟩
    rw [setSyntaxEnumerate_code]
    exact ⟨values, ht, hp⟩

/-- All first-order satisfaction over the set D is one actual set in M.
The proof joins genuine finite-formula sections using the maintained countable closure.
It makes no assertion about satisfaction for the ambient proper class. -/
theorem ModelStage.setSatisfaction_mem (stage : ModelStage.{u}) (D : stage.model.Element) :
    setSatisfaction D.val ∈ stage.model.carrier := by
  obtain ⟨result, hr⟩ := stage.countableUnion_exists
    (fun n => stage.satisfactionSection D (setSyntaxEnumerate n).2)
  have same : result.val = setSatisfaction D.val := by
    apply ZFSet.ext
    intro p
    exact (hr p).trans (stage.mem_satisfactionSections_iff D p)
  rw [← same]
  exact result.property

noncomputable def ModelStage.setSatisfaction (stage : ModelStage.{u})
    (D : stage.model.Element) : stage.model.Element := ⟨IBLP.setSatisfaction D.val, stage.setSatisfaction_mem D⟩

theorem ModelStage.setSatisfaction_realize (stage : ModelStage.{u})
    (D : stage.model.Element) {n : Nat} (phi : RankPredicateFormula 0 n)
    (values : Fin n → SetDomain D.val) :
    ZFSet.pair (rankSyntaxCode ⟨n, phi⟩ : Ordinal).toZFSet (setAssignment values) ∈
      (stage.setSatisfaction D).val ↔ SetDomain.realize D.val phi values :=
  IBLP.setSatisfaction_realize D.val phi values

end IBLP
