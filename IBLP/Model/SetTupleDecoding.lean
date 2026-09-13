import IBLP.Model.SetSatisfactionFormulaAtoms

namespace IBLP
open FullMarkedBLP
universe u

theorem setTuple_injective {n : Nat} : Function.Injective (@setTuple.{u} n) := by
  intro xs ys h
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    have parts := ZFSet.pair_inj.mp h
    have tail := ih parts.2
    funext i
    exact Fin.cases parts.1 (fun j => congrFun tail j) i

theorem setTuple_mem_natRelation {n : Nat} (relation : (Fin n → Nat) → Prop)
    (xs : Fin n → ZFSet.{u}) :
    setTuple xs ∈ zfNatRelation relation ↔
      ∃ ns : Fin n → Nat, relation ns ∧ xs = fun i => (ns i : Ordinal.{u}).toZFSet := by
  rw [zfNatRelation, ZFSet.mem_range]
  constructor
  · rintro ⟨⟨ns, hns⟩, he⟩
    rw [← setTuple_nat] at he
    exact ⟨ns, hns, (setTuple_injective he).symm⟩
  · rintro ⟨ns, hns, rfl⟩
    exact ⟨⟨ns, hns⟩, (setTuple_nat ns).symm⟩

theorem setArityTable_iff (code arity : ZFSet.{u}) :
    setTuple ![code, arity] ∈ zfNatRelation rankSyntaxArity ↔
      ∃ (n : Nat) (phi : RankPredicateFormula 0 n),
        code = (rankSyntaxCode ⟨n, phi⟩ : Ordinal).toZFSet ∧ arity = (n : Ordinal).toZFSet := by
  rw [setTuple_mem_natRelation]
  constructor
  · rintro ⟨tuple, ⟨⟨n, phi⟩, hc, ha⟩, coords⟩
    refine ⟨n, phi, ?_, ?_⟩
    · simpa [hc] using congrFun coords 0
    · simpa [ha] using congrFun coords 1
  · rintro ⟨n, phi, rfl, rfl⟩
    refine ⟨![rankSyntaxCode ⟨n, phi⟩, n], ⟨⟨n, phi⟩, rfl, rfl⟩, ?_⟩
    funext i
    fin_cases i <;> rfl

theorem setFalseTable_iff (code : ZFSet.{u}) :
    setTuple ![code] ∈ zfNatRelation rankSyntaxFalse ↔
      ∃ n, code = (rankSyntaxCode ⟨n, .falsum⟩ : Ordinal).toZFSet := by
  rw [setTuple_mem_natRelation]
  constructor
  · rintro ⟨tuple, ⟨n, hc⟩, coords⟩
    exact ⟨n, by simpa [hc] using congrFun coords 0⟩
  · rintro ⟨n, rfl⟩
    refine ⟨![rankSyntaxCode ⟨n, .falsum⟩], ⟨n, rfl⟩, ?_⟩
    funext i
    fin_cases i
    rfl

theorem setEqualTable_iff (code i j : ZFSet.{u}) :
    setTuple ![code, i, j] ∈ zfNatRelation rankSyntaxEqual ↔
      ∃ (n : Nat) (x y : Fin n), code = (rankSyntaxCode ⟨n, .equal x y⟩ : Ordinal).toZFSet ∧
        i = (x.val : Ordinal).toZFSet ∧ j = (y.val : Ordinal).toZFSet := by
  rw [setTuple_mem_natRelation]
  constructor
  · rintro ⟨tuple, ⟨n, x, y, hc, hi, hj⟩, coords⟩
    refine ⟨n, x, y, ?_, ?_, ?_⟩
    · simpa [hc] using congrFun coords 0
    · simpa [hi] using congrFun coords 1
    · simpa [hj] using congrFun coords 2
  · rintro ⟨n, x, y, rfl, rfl, rfl⟩
    refine ⟨![rankSyntaxCode ⟨n, .equal x y⟩, x.val, y.val], ⟨n, x, y, rfl, rfl, rfl⟩, ?_⟩
    funext i
    fin_cases i <;> rfl

theorem setMemberTable_iff (code i j : ZFSet.{u}) :
    setTuple ![code, i, j] ∈ zfNatRelation rankSyntaxMember ↔
      ∃ (n : Nat) (x y : Fin n), code = (rankSyntaxCode ⟨n, .member x y⟩ : Ordinal).toZFSet ∧
        i = (x.val : Ordinal).toZFSet ∧ j = (y.val : Ordinal).toZFSet := by
  rw [setTuple_mem_natRelation]
  constructor
  · rintro ⟨tuple, ⟨n, x, y, hc, hi, hj⟩, coords⟩
    refine ⟨n, x, y, ?_, ?_, ?_⟩
    · simpa [hc] using congrFun coords 0
    · simpa [hi] using congrFun coords 1
    · simpa [hj] using congrFun coords 2
  · rintro ⟨n, x, y, rfl, rfl, rfl⟩
    refine ⟨![rankSyntaxCode ⟨n, .member x y⟩, x.val, y.val], ⟨n, x, y, rfl, rfl, rfl⟩, ?_⟩
    funext i
    fin_cases i <;> rfl

theorem setImpTable_iff (code p q : ZFSet.{u}) :
    setTuple ![code, p, q] ∈ zfNatRelation rankSyntaxImp ↔
      ∃ (n : Nat) (left right : RankPredicateFormula 0 n),
        code = (rankSyntaxCode ⟨n, .imp left right⟩ : Ordinal).toZFSet ∧
        p = (rankSyntaxCode ⟨n, left⟩ : Ordinal).toZFSet ∧
        q = (rankSyntaxCode ⟨n, right⟩ : Ordinal).toZFSet := by
  rw [setTuple_mem_natRelation]
  constructor
  · rintro ⟨tuple, ⟨n, left, right, hc, hp, hq⟩, coords⟩
    refine ⟨n, left, right, ?_, ?_, ?_⟩
    · simpa [hc] using congrFun coords 0
    · simpa [hp] using congrFun coords 1
    · simpa [hq] using congrFun coords 2
  · rintro ⟨n, left, right, rfl, rfl, rfl⟩
    refine ⟨![rankSyntaxCode ⟨n, .imp left right⟩, rankSyntaxCode ⟨n, left⟩,
      rankSyntaxCode ⟨n, right⟩], ⟨n, left, right, rfl, rfl, rfl⟩, ?_⟩
    funext i
    fin_cases i <;> rfl

theorem setAllTable_iff (code body : ZFSet.{u}) :
    setTuple ![code, body] ∈ zfNatRelation rankSyntaxAll ↔
      ∃ (n : Nat) (phi : RankPredicateFormula 0 (n + 1)),
        code = (rankSyntaxCode ⟨n, .all phi⟩ : Ordinal).toZFSet ∧
        body = (rankSyntaxCode ⟨n + 1, phi⟩ : Ordinal).toZFSet := by
  rw [setTuple_mem_natRelation]
  constructor
  · rintro ⟨tuple, ⟨n, phi, hc, hp⟩, coords⟩
    refine ⟨n, phi, ?_, ?_⟩
    · simpa [hc] using congrFun coords 0
    · simpa [hp] using congrFun coords 1
  · rintro ⟨n, phi, rfl, rfl⟩
    refine ⟨![rankSyntaxCode ⟨n, .all phi⟩, rankSyntaxCode ⟨n + 1, phi⟩],
      ⟨n, phi, rfl, rfl⟩, ?_⟩
    funext i
    fin_cases i <;> rfl

end IBLP
