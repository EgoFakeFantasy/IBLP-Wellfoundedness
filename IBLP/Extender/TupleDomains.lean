import IBLP.Extender.FiniteSeeds

namespace IBLP.Extender
open FullMarkedBLP
universe u

/-- The actual finite product, using nested Kuratowski pairs and empty tail. -/
def CodedTuple (domain : ZFSet.{u}) : Nat → ZFSet.{u} → Prop
  | 0, z => z = ∅
  | n + 1, z => ∃ a ∈ domain, ∃ tail, CodedTuple domain n tail ∧ z = ZFSet.pair a tail

def tupleDomainFormula : Nat → RankPredicateFormula 0 2
  | 0 => rankFormulaEmpty 1
  | n + 1 => ((RankPredicateFormula.member 2 0).and
      (((tupleDomainFormula n).relabelSets ![0, 3]).and (rankFormulaOrderedPair 1 2 3))).ex.ex

theorem tupleDomainFormula_realize (M : TransitiveClass.{u}) (n : Nat) (domain z : M.Element) :
    M.realize (tupleDomainFormula n) ![domain, z] ↔ CodedTuple domain.val n z.val := by
  induction n generalizing z with
  | zero => exact M.setEmptyAtom_realize _ _
  | succ n ih =>
    have sem : M.realize (tupleDomainFormula (n + 1)) ![domain, z] ↔
        ∃ a tail : M.Element, a.val ∈ domain.val ∧ CodedTuple domain.val n tail.val ∧
          z.val = ZFSet.pair a.val tail.val := by
      simp only [tupleDomainFormula, M.realize_ex, M.realize_and, M.realize_relabel,
        M.setOrderedPairAtom_realize]
      apply exists_congr
      intro a
      apply exists_congr
      intro tail
      have args : Fin.snoc (Fin.snoc ![domain, z] a) tail ∘ ![0, 3] = ![domain, tail] := by
        funext i; fin_cases i <;> rfl
      rw [args, ih]
      rfl
    rw [sem]
    constructor
    · rintro ⟨a, tail, ha, ht, same⟩
      exact ⟨a.val, ha, tail.val, ht, same⟩
    · rintro ⟨a, ha, tail, ht, same⟩
      have inside := M.pair_components (same ▸ z.property)
      exact ⟨⟨a, inside.1⟩, ⟨tail, inside.2⟩, ha, ht, same⟩

theorem codedTuple_setTuple {domain : ZFSet.{u}} {n : Nat} (xs : Fin n → ZFSet.{u})
    (inside : ∀ i, xs i ∈ domain) : CodedTuple domain n (setTuple xs) := by
  induction n with
  | zero => rfl
  | succ n ih => exact ⟨xs 0, inside 0, setTuple (fun i : Fin n => xs i.succ),
      ih _ (fun i => inside i.succ), rfl⟩

theorem codedTuple_iff {domain z : ZFSet.{u}} {n : Nat} :
    CodedTuple domain n z ↔ ∃ xs : Fin n → ZFSet.{u}, (∀ i, xs i ∈ domain) ∧ z = setTuple xs := by
  constructor
  · intro h
    induction n generalizing z with
    | zero => exact ⟨Fin.elim0, fun i => Fin.elim0 i, h⟩
    | succ n ih =>
      obtain ⟨a, ha, tail, ht, same⟩ := h
      obtain ⟨xs, inside, rfl⟩ := ih ht
      exact ⟨Fin.cons a xs, fun i => Fin.cases ha inside i, same⟩
  · rintro ⟨xs, inside, rfl⟩
    exact codedTuple_setTuple xs inside

namespace Derivation
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}

noncomputable def tupleDomain (n : Nat) : Test stage alpha :=
  let result := stage.separation (tupleDomainFormula n) ![stage.hierarchy alpha] (stage.hierarchy alpha)
  ⟨result.val, result.property, Order.lt_succ_of_le (by
    apply (ZFSet.rank_mono (show result.val ⊆ (stage.hierarchy alpha).val from ?_)).trans_eq
      (stage.hierarchy_rank alpha)
    intro z hz
    exact ((stage.mem_separation _ _ _ (stage.model.member result z hz)).mp hz).1)⟩

theorem mem_tupleDomain (n : Nat) (z : ZFSet.{u}) :
    z ∈ (tupleDomain (stage := stage) (alpha := alpha) n).val ↔
      z ∈ (stage.hierarchy alpha).val ∧ CodedTuple (stage.hierarchy alpha).val n z := by
  let result := stage.separation (tupleDomainFormula n) ![stage.hierarchy alpha] (stage.hierarchy alpha)
  have spec (x : stage.model.Element) : x.val ∈ result.val ↔ x.val ∈ (stage.hierarchy alpha).val ∧
      CodedTuple (stage.hierarchy alpha).val n x.val := by
    rw [stage.mem_separation]
    have args : Fin.snoc ![stage.hierarchy alpha] x = ![stage.hierarchy alpha, x] := by
      funext i; fin_cases i <;> rfl
    rw [args, tupleDomainFormula_realize]
  constructor
  · intro hz
    exact (spec (stage.model.member result z hz)).mp hz
  · intro hz
    exact (spec (stage.model.member (stage.hierarchy alpha) z hz.1)).mpr hz

def tupleDomainMatrix (n : Nat) : RankPredicateFormula 0 2 :=
  .all ((RankPredicateFormula.member 2 1).iff
    ((RankPredicateFormula.member 2 0).and ((tupleDomainFormula n).relabelSets ![0, 2])))

theorem tupleDomainMatrix_realize (M : TransitiveClass.{u}) (n : Nat) (domain result : M.Element) :
    M.realize (tupleDomainMatrix n) ![domain, result] ↔
      ∀ x : M.Element, x.val ∈ result.val ↔ x.val ∈ domain.val ∧ CodedTuple domain.val n x.val := by
  change (∀ x, M.realize _ (Fin.snoc ![domain, result] x)) ↔ _
  apply forall_congr'
  intro x
  rw [M.pure_iff_realize, M.realize_and, M.realize_relabel]
  have args : Fin.snoc ![domain, result] x ∘ ![0, 2] = ![domain, x] := by
    funext i; fin_cases i <;> rfl
  rw [args, tupleDomainFormula_realize]
  rfl

theorem map_tupleDomain (D : Derivation stage alpha beta) (n : Nat) :
    D.map (tupleDomain n) = tupleDomain n := by
  have source : (stage.model.rankPart (Order.succ alpha)).realize (tupleDomainMatrix n)
      ![top, tupleDomain n] := by
    apply (tupleDomainMatrix_realize _ _ _ _).mpr
    intro x
    exact mem_tupleDomain n x.val
  have image := (D.map.realize_iff (tupleDomainMatrix n) ![top, tupleDomain n]).mpr source
  have args : D.map ∘ ![top, tupleDomain n] = ![D.map top, D.map (tupleDomain n)] := by
    funext i; fin_cases i <;> rfl
  rw [args] at image
  apply (stage.model.rankPart (Order.succ beta)).element_ext
  intro x
  have h := (tupleDomainMatrix_realize _ _ _ _).mp image x
  change _ ↔ x.val ∈ (D.map (stage.rankHierarchy (endpoint alpha))).val ∧
    CodedTuple (D.map (stage.rankHierarchy (endpoint alpha))).val n x.val at h
  rw [stage.boundedMap_top] at h
  exact h.trans (mem_tupleDomain n x.val).symm

theorem tupleSeed_mem_tupleDomain (limit : Order.IsSuccLimit beta) {n : Nat}
    (seeds : Fin n → Seed stage beta) :
    (tupleSeed limit seeds).val ∈ (tupleDomain (stage := stage) (alpha := beta) n).val := by
  apply (mem_tupleDomain _ _).mpr
  refine ⟨(stage.mem_hierarchy beta _).mpr (tupleSeed limit seeds).property, ?_⟩
  rw [tupleSeed_val]
  exact codedTuple_setTuple _ (fun i => (stage.mem_hierarchy beta _).mpr (seeds i).property)

/-- At a limit rank, the cut loses no finite tuple: the constructed domain
is exactly the full finite product of the actual internal rank. -/
theorem tupleDomain_full_product (limit : Order.IsSuccLimit alpha) (n : Nat) (z : ZFSet.{u}) :
    z ∈ (tupleDomain (stage := stage) (alpha := alpha) n).val ↔
      ∃ entries : Fin n → Seed stage alpha, (tupleSeed limit entries).val = z := by
  constructor
  · intro hz
    obtain ⟨xs, inside, same⟩ := codedTuple_iff.mp ((mem_tupleDomain n z).mp hz).2
    let entries : Fin n → Seed stage alpha := fun i =>
      ⟨xs i, (stage.mem_hierarchy alpha (xs i)).mp (inside i)⟩
    refine ⟨entries, ?_⟩
    rw [tupleSeed_val]
    exact same.symm
  · rintro ⟨entries, rfl⟩
    exact tupleSeed_mem_tupleDomain limit entries

theorem large_tupleDomain (D : Derivation stage alpha beta) (limit : Order.IsSuccLimit beta)
    {n : Nat} (seeds : Fin n → Seed stage beta) : D.Large (tupleSeed limit seeds) (tupleDomain n) := by
  change (tupleSeed limit seeds).val ∈ (D.map (tupleDomain n)).val
  rw [D.map_tupleDomain]
  exact tupleSeed_mem_tupleDomain limit seeds

end Derivation
end IBLP.Extender
