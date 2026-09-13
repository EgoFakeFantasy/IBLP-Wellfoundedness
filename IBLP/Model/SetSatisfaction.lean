import IBLP.Model.Relativization
import FullMarkedBLP.RankSyntaxData
import FullMarkedBLP.RankFiniteAssignment

namespace IBLP
open FullMarkedBLP
universe u

/-- Finite assignment graphs have their actual finite ordinal as domain. -/
noncomputable def setAssignment {D : ZFSet.{u}} {n : Nat}
    (values : Fin n → SetDomain D) : ZFSet.{u} :=
  ZFSet.range (fun i : Fin n => ZFSet.pair (i.val : Ordinal).toZFSet (values i).val)

theorem mem_setAssignment {D : ZFSet.{u}} {n : Nat}
    (values : Fin n → SetDomain D) (p : ZFSet.{u}) :
    p ∈ setAssignment values ↔
      ∃ i : Fin n, p = ZFSet.pair (i.val : Ordinal).toZFSet (values i).val := by
  simp only [setAssignment, ZFSet.mem_range]
  exact exists_congr (fun _ => eq_comm)

theorem setAssignment_applies_iff {D : ZFSet.{u}} {n : Nat}
    (values : Fin n → SetDomain D) (a b : ZFSet.{u}) :
    ZFSet.pair a b ∈ setAssignment values ↔
      ∃ i : Fin n, a = (i.val : Ordinal).toZFSet ∧ b = (values i).val := by
  simp only [mem_setAssignment, ZFSet.pair_inj]

theorem setAssignment_injective {D : ZFSet.{u}} {n : Nat} :
    Function.Injective (@setAssignment D n) := by
  intro v w same
  funext i
  have edge : ZFSet.pair (i.val : Ordinal).toZFSet (v i).val ∈ setAssignment v :=
    (mem_setAssignment _ _).mpr ⟨i, rfl⟩
  rw [same] at edge
  obtain ⟨j, hi, hv⟩ := (setAssignment_applies_iff _ _ _).mp edge
  have hij : i = j := Fin.ext (Nat.cast_injective (Ordinal.toZFSet_injective hi))
  subst j
  exact Subtype.ext hv

theorem setAssignment_snoc {D : ZFSet.{u}} {n : Nat}
    (values : Fin n → SetDomain D) (x : SetDomain D) :
    setAssignment (Fin.snoc values x) =
      setAssignment values ∪ {ZFSet.pair (n : Ordinal).toZFSet x.val} := by
  apply ZFSet.ext
  intro p
  simp only [mem_setAssignment, ZFSet.mem_union, ZFSet.mem_singleton]
  constructor
  · rintro ⟨i, hi⟩
    cases i using Fin.lastCases with
    | last => exact Or.inr (by simpa using hi)
    | cast i => exact Or.inl ⟨i, by simpa using hi⟩
  · rintro (⟨i, hi⟩ | hi)
    · exact ⟨i.castSucc, by simpa using hi⟩
    · exact ⟨Fin.last n, by simpa using hi⟩

/-- All correctly encoded true formula/assignment pairs over one actual set.
The definition uses set separation with an explicit set bound, not universe truth. -/
noncomputable def setSatisfaction (D : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun pair => ∃ (n : Nat) (phi : RankPredicateFormula 0 n)
    (values : Fin n → SetDomain D),
    pair = ZFSet.pair (rankSyntaxCode ⟨n, phi⟩ : Ordinal).toZFSet (setAssignment values) ∧
      SetDomain.realize D phi values)
    (ZFSet.prod Ordinal.omega0.toZFSet
      (ZFSet.powerset (ZFSet.prod Ordinal.omega0.toZFSet D)))

theorem setAssignment_subset {D : ZFSet.{u}} {n : Nat}
    (values : Fin n → SetDomain D) :
    setAssignment values ⊆ ZFSet.prod Ordinal.omega0.toZFSet D := by
  intro p hp
  obtain ⟨i, rfl⟩ := (mem_setAssignment _ _).mp hp
  exact ZFSet.pair_mem_prod.mpr
    ⟨Ordinal.toZFSet_mem_toZFSet_iff.mpr (Ordinal.natCast_lt_omega0 _), (values i).property⟩

theorem setSatisfaction_realize (D : ZFSet.{u}) {n : Nat}
    (phi : RankPredicateFormula 0 n) (values : Fin n → SetDomain D) :
    ZFSet.pair (rankSyntaxCode ⟨n, phi⟩ : Ordinal).toZFSet (setAssignment values) ∈
      setSatisfaction D ↔ SetDomain.realize D phi values := by
  rw [setSatisfaction, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, m, psi, other, same, truth⟩
    have parts := ZFSet.pair_inj.mp same
    have codes := rankSyntaxCode_injective
      (Nat.cast_injective (Ordinal.toZFSet_injective parts.1))
    have arity : n = m := (Sigma.mk.inj codes).1
    subst m
    have formula : phi = psi := eq_of_heq (Sigma.mk.inj codes).2
    subst psi
    have assignment := setAssignment_injective parts.2
    rwa [← assignment] at truth
  · intro truth
    refine ⟨ZFSet.pair_mem_prod.mpr ⟨?_, ?_⟩, n, phi, values, rfl, truth⟩
    · exact Ordinal.toZFSet_mem_toZFSet_iff.mpr (Ordinal.natCast_lt_omega0 _)
    · exact ZFSet.mem_powerset.mpr (setAssignment_subset values)

/-- The five semantic recursion clauses quantify only over the given set D. -/
structure SetTruthConditions (D truth : ZFSet.{u}) : Prop where
  falsum : ∀ (n : Nat) (v : Fin n → SetDomain D),
    ZFSet.pair (rankSyntaxCode ⟨n, .falsum⟩ : Ordinal).toZFSet (setAssignment v) ∉ truth
  equal : ∀ (n : Nat) (x y : Fin n) (v : Fin n → SetDomain D),
    ZFSet.pair (rankSyntaxCode ⟨n, .equal x y⟩ : Ordinal).toZFSet (setAssignment v) ∈ truth ↔ v x = v y
  member : ∀ (n : Nat) (x y : Fin n) (v : Fin n → SetDomain D),
    ZFSet.pair (rankSyntaxCode ⟨n, .member x y⟩ : Ordinal).toZFSet (setAssignment v) ∈ truth ↔
      (v x).val ∈ (v y).val
  imp : ∀ (n : Nat) (p q : RankPredicateFormula 0 n) (v : Fin n → SetDomain D),
    ZFSet.pair (rankSyntaxCode ⟨n, .imp p q⟩ : Ordinal).toZFSet (setAssignment v) ∈ truth ↔
      (ZFSet.pair (rankSyntaxCode ⟨n, p⟩ : Ordinal).toZFSet (setAssignment v) ∈ truth →
        ZFSet.pair (rankSyntaxCode ⟨n, q⟩ : Ordinal).toZFSet (setAssignment v) ∈ truth)
  all : ∀ (n : Nat) (p : RankPredicateFormula 0 (n + 1)) (v : Fin n → SetDomain D),
    ZFSet.pair (rankSyntaxCode ⟨n, .all p⟩ : Ordinal).toZFSet (setAssignment v) ∈ truth ↔
      ∀ x : SetDomain D,
        ZFSet.pair (rankSyntaxCode ⟨n + 1, p⟩ : Ordinal).toZFSet (setAssignment (Fin.snoc v x)) ∈ truth

theorem setSatisfaction_conditions (D : ZFSet.{u}) : SetTruthConditions D (setSatisfaction D) := by
  constructor
  · intro n v
    rw [setSatisfaction_realize]
    exact id
  · intro n x y v
    exact setSatisfaction_realize D _ _
  · intro n x y v
    exact setSatisfaction_realize D _ _
  · intro n p q v
    simp only [setSatisfaction_realize, SetDomain.realize]
  · intro n p v
    simp only [setSatisfaction_realize, SetDomain.realize]

/-- Any set satisfying the recursion clauses gives actual truth at valid codes. -/
theorem SetTruthConditions.realize {D truth : ZFSet.{u}} (h : SetTruthConditions D truth)
    {n : Nat} (phi : RankPredicateFormula 0 n) (v : Fin n → SetDomain D) :
    ZFSet.pair (rankSyntaxCode ⟨n, phi⟩ : Ordinal).toZFSet (setAssignment v) ∈ truth ↔
      SetDomain.realize D phi v := by
  induction phi with
  | falsum => exact iff_false_intro (h.falsum _ v)
  | equal x y => exact h.equal _ x y v
  | member x y => exact h.member _ x y v
  | predicate a _ => exact Fin.elim0 a
  | imp p q ihp ihq => exact (h.imp _ p q v).trans (imp_congr (ihp v) (ihq v))
  | all p ih => exact (h.all _ p v).trans (forall_congr' (fun x => ih (Fin.snoc v x)))

end IBLP
