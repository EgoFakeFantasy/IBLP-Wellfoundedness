import IBLP.Model.Inaccessible
import FullMarkedBLP.ZFFunctionEquiv
import FullMarkedBLP.RankCardinalCharacterization
import Mathlib.SetTheory.Cardinal.Regular

namespace IBLP
open FullMarkedBLP
universe u

theorem setGraphOnto.card_le {f x y : ZFSet.{u}} (function : ZFSet.IsFunc x y f)
    (onto : setGraphOnto f x y) : y.card ≤ x.card := by
  have surj : Function.Surjective (zfGraphFunction function) := by
    intro b
    obtain ⟨a, ha, hab⟩ := onto b.val b.property
    exact ⟨⟨a, ha⟩, zfGraphFunction_unique function ⟨a, ha⟩ b hab⟩
  simpa only [ZFSet.cardinalMk_coe_sort, Cardinal.lift_le] using Cardinal.mk_le_of_surjective surj

/-- An ambient initial ordinal admits no internal smaller-domain surjection.
The converse is intentionally stated only for the full initial universe. -/
theorem TransitiveClass.internalInitial_of_ambient (M : TransitiveClass.{u})
    (k : M.Element) (ordinal : ZFSet.IsOrdinal k.val)
    (initial : ∃ c : Cardinal.{u}, c.ord = k.val.rank) : M.InternalInitial k := by
  obtain ⟨c, hc⟩ := initial
  refine ⟨ordinal, ?_⟩
  intro a ha f hf
  have arep := ordinal.mem ha
  have arank : a.val.rank < c.ord := by
    rw [hc]
    exact ZFSet.rank_lt_of_mem ha
  have acard : a.val.card < c := by
    have h := Cardinal.lt_ord.mp arank
    have eqCard : a.val.card = a.val.rank.card := by
      calc
        a.val.card = a.val.rank.toZFSet.card := congrArg ZFSet.card arep.toZFSet_rank_eq.symm
        _ = a.val.rank.card := Ordinal.card_toZFSet _
    rw [eqCard]
    exact h
  have kcard : k.val.card = c := by
    rw [← ordinal.toZFSet_rank_eq, ← hc, Ordinal.card_toZFSet, Cardinal.card_ord]
  have hle := hf.2.card_le hf.1
  rw [kcard] at hle
  exact (not_lt_of_ge hle) acard

theorem universe_internalInitial_iff (k : universeClass.{u}.toTransitiveClass.Element) :
    universeClass.toTransitiveClass.InternalInitial k ↔
      ZFSet.IsOrdinal k.val ∧ ∃ c : Cardinal.{u}, c.ord = k.val.rank := by
  constructor
  · intro initial
    refine ⟨initial.1, (ordinal_cardinal_iff_no_smaller_equinumerous k.val.rank).mpr ?_⟩
    intro a ha heq
    let domain : universeClass.{u}.toTransitiveClass.Element := ⟨a.toZFSet, Set.mem_univ _⟩
    have smaller : domain.val ∈ k.val := by
      rw [← initial.1.toZFSet_rank_eq]
      exact Ordinal.toZFSet_mem_toZFSet_iff.mpr ha
    have cardEq : domain.val.card = k.val.card := by
      rw [← initial.1.toZFSet_rank_eq]
      simpa only [domain, Ordinal.card_toZFSet] using heq
    have hm : Cardinal.mk domain.val = Cardinal.mk k.val := by
      rw [ZFSet.cardinalMk_coe_sort, ZFSet.cardinalMk_coe_sort, cardEq]
    obtain ⟨e⟩ := Cardinal.eq.mp hm
    exact initial.2 domain smaller ⟨zfFunctionGraph e, Set.mem_univ _⟩
      ⟨zfFunctionGraph_isFunc e, zfFunctionGraph_onto e e.surjective⟩
  · rintro ⟨ordinal, initial⟩
    exact universeClass.toTransitiveClass.internalInitial_of_ambient k ordinal initial

/-- The fact that an internally uncountable initial ordinal is a limit is
transferred as a single finite formula. It does not identify internal cardinals
with ambient cardinals in later models. -/
theorem ModelStage.internalInitial_uncountable_isSuccLimit (stage : ModelStage.{u})
    (k : stage.model.Element) (initial : stage.model.InternalInitial k)
    (uncountable : stage.model.InternalUncountable k) : Order.IsSuccLimit k.val.rank := by
  let phi := (internalInitialFormula.and internalUncountableFormula).imp
    (rankPredicateAtom rankNonzeroLimitFormula ![0])
  have sem (M : TransitiveClass.{u}) (x : M.Element) : M.realize phi ![x] ↔
      (M.InternalInitial x ∧ M.InternalUncountable x → setNonzeroLimit x.val) := by
    change (M.realize (internalInitialFormula.and internalUncountableFormula) ![x] → _) ↔ _
    rw [M.realize_and, M.internalInitialFormula_realize, M.internalUncountableFormula_realize]
    apply imp_congr Iff.rfl
    rw [M.realize_atom]
    have tuple : ![x] ∘ ![(0 : Fin 1)] = ![x] := by funext i; fin_cases i; rfl
    rw [tuple, M.nonzeroLimitFormula_absolute]
  have valid : ∀ v, universeClass.{u}.toTransitiveClass.realize phi v := by
    intro v
    have tuple : v = ![v 0] := by funext i; fin_cases i; rfl
    rw [tuple]
    apply (sem _ _).mpr
    rintro ⟨hi, hu⟩
    obtain ⟨ordinal, c, hc⟩ := universe_internalInitial_iff _ |>.mp hi
    have above := (universeClass.toTransitiveClass.internalUncountable_ordinal_iff _ ordinal).mp hu
    have infinite : Cardinal.aleph0 ≤ c := by
      apply Cardinal.ord_le_ord.mp
      rw [Cardinal.ord_aleph0, hc]
      exact above.le
    have limit : Order.IsSuccLimit (v 0).val.rank := by
      rw [← hc]
      exact Cardinal.isSuccLimit_ord infinite
    rw [← ordinal.toZFSet_rank_eq]
    exact (setNonzeroLimit_ordinal_iff _).mpr limit
  have h := (sem _ _).mp (stage.transfer_schema phi valid ![k]) ⟨initial, uncountable⟩
  apply (setNonzeroLimit_ordinal_iff _).mp
  rw [initial.1.toZFSet_rank_eq]
  exact h

theorem ModelStage.internalInaccessible_isSuccLimit (stage : ModelStage.{u})
    (k : stage.model.Element) (h : stage.model.InternalInaccessible k) : Order.IsSuccLimit k.val.rank :=
  stage.internalInitial_uncountable_isSuccLimit k h.1 h.2.1

theorem setGraphCofinal.not_of_regular {f x : ZFSet.{u}} {c : Cardinal.{u}}
    (regular : Cardinal.IsRegular c) (small : x.card < c)
    (function : ZFSet.IsFunc x c.ord.toZFSet f) : ¬setGraphCofinal f x c.ord.toZFSet := by
  intro cofinal
  let g (i : Shrink x) : Ordinal.{u} :=
    (zfGraphFunction function ((equivShrink x).symm i)).val.rank
  have hg (i : Shrink x) : g i < c.ord := by
    simpa only [g, Ordinal.rank_toZFSet] using
      ZFSet.rank_lt_of_mem (zfGraphFunction function ((equivShrink x).symm i)).property
  have hcard : Cardinal.mk (Shrink x) < c.ord.cof := by
    rw [regular.cof_ord]
    exact small
  have bound := Ordinal.iSup_lt_of_lt_cof hcard hg
  obtain ⟨a, ha, y, hy, edge, above⟩ :=
    cofinal (iSup g).toZFSet (Ordinal.toZFSet_mem_toZFSet_iff.mpr bound)
  have value := zfGraphFunction_unique function ⟨a, ha⟩ ⟨y, hy⟩ edge
  have greater : iSup g < y.rank := by
    simpa only [Ordinal.rank_toZFSet] using ZFSet.rank_lt_of_mem above
  have upper : y.rank ≤ iSup g := by
    calc
      y.rank = g (equivShrink x ⟨a, ha⟩) := by
        simp only [g, Equiv.symm_apply_apply]
        exact congrArg (fun z : c.ord.toZFSet => z.val.rank) value.symm
      _ ≤ iSup g := Ordinal.le_iSup g _
  exact (not_lt_of_ge upper) greater

/-- The ambient-to-internal bridge is a proved implication, not the definition
of internal inaccessibility. In later inner models only their own graph tests
are used. Both ambient initiality and ambient inaccessibility are explicit. -/
theorem TransitiveClass.internalInaccessible_of_ambient (M : TransitiveClass.{u})
    (k : M.Element) (ordinal : ZFSet.IsOrdinal k.val)
    (initial : ∃ c : Cardinal.{u}, c.ord = k.val.rank)
    (inaccessible : Cardinal.IsInaccessible k.val.rank.card) : M.InternalInaccessible k := by
  obtain ⟨c, hc⟩ := initial
  have cardEq : k.val.rank.card = c := by rw [← hc, Cardinal.card_ord]
  have inaccessible' : Cardinal.IsInaccessible c := cardEq ▸ inaccessible
  have rep : k.val = c.ord.toZFSet := by rw [hc]; exact ordinal.toZFSet_rank_eq.symm
  have kcard : k.val.card = c := by rw [rep, Ordinal.card_toZFSet, Cardinal.card_ord]
  have smallerCard (a : M.Element) (ha : a.val ∈ k.val) : a.val.card < c := by
    have ordinalA := ordinal.mem ha
    have lower : a.val.rank < c.ord := by rw [hc]; exact ZFSet.rank_lt_of_mem ha
    have eqCard : a.val.card = a.val.rank.card := by
      calc
        a.val.card = a.val.rank.toZFSet.card := congrArg ZFSet.card ordinalA.toZFSet_rank_eq.symm
        _ = a.val.rank.card := Ordinal.card_toZFSet _
    rw [eqCard]
    exact Cardinal.lt_ord.mp lower
  refine ⟨M.internalInitial_of_ambient k ordinal ⟨c, hc⟩, ?_, ?_, ?_⟩
  · apply (M.internalUncountable_iff k).mpr
    rw [rep, Ordinal.toZFSet_mem_toZFSet_iff, ← Cardinal.ord_aleph0]
    exact Cardinal.ord_lt_ord.mpr (Cardinal.isInaccessible_def.mp inaccessible').1
  · intro a ha f hf
    have function : ZFSet.IsFunc a.val c.ord.toZFSet f.val := by rw [← rep]; exact hf.1
    have cofinal : setGraphCofinal f.val a.val c.ord.toZFSet := by rw [← rep]; exact hf.2
    exact cofinal.not_of_regular inaccessible'.isRegular (smallerCard a ha) function
  · intro a ha p hp f hf
    have subset : p.val ⊆ ZFSet.powerset a.val := by
      intro z hz
      exact ZFSet.mem_powerset.mpr ((hp (M.member p z hz)).mp hz)
    have pcard : p.val.card < c := by
      apply (ZFSet.card_mono subset).trans_lt
      rw [ZFSet.card_powerset]
      exact inaccessible'.isStrongLimit.isStrongPrelimit (smallerCard a ha)
    have large := hf.2.card_le hf.1
    rw [kcard] at large
    exact (not_lt_of_ge large) pcard

theorem ModelStage.internalStrongLimit_iff_powerset (stage : ModelStage.{u})
    (k : stage.model.Element) : stage.model.InternalStrongLimit k ↔
      ∀ a : stage.model.Element, a.val ∈ k.val → ∀ f : stage.model.Element,
        ¬(ZFSet.IsFunc (stage.powerset a).val k.val f.val ∧
          setGraphOnto f.val (stage.powerset a).val k.val) := by
  constructor
  · intro h a ha f hf
    exact h a ha (stage.powerset a) (stage.mem_powerset a) f hf
  · intro h a ha p hp f hf
    have same : p = stage.powerset a := by
      apply stage.model.element_ext
      intro z
      exact (hp z).trans (stage.mem_powerset a z).symm
    subst p
    exact h a ha f hf

theorem ModelStage.ordinal_internalInaccessible_of_ambient (stage : ModelStage.{u})
    (kappa : Ordinal.{u}) (initial : ∃ c : Cardinal.{u}, c.ord = kappa)
    (inaccessible : Cardinal.IsInaccessible kappa.card) :
    stage.model.InternalInaccessible (stage.ordinal kappa) := by
  apply stage.model.internalInaccessible_of_ambient _ (ZFSet.isOrdinal_toZFSet _)
  · simpa only [ModelStage.ordinal, Ordinal.rank_toZFSet] using initial
  · simpa only [ModelStage.ordinal, Ordinal.rank_toZFSet] using inaccessible

end IBLP
