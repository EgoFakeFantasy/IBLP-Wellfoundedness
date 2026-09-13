import IBLP.Trace
import IBLP.Rank.PrefixBounds
import IBLP.Rank.WeakEdges

namespace IBLP
universe u v

/-- The historical factor list, ordered outermost first. The terminal paired
source is not a factor. This relation only records the existing p edges. -/
inductive FactorTrace (a : Pattern) (target : Nat) : Nat → List Nat → Prop
  | single {start} : predecessor a start = some target → target < start →
      FactorTrace a target start [start]
  | cons {start next tail} : predecessor a start = some next → next < start →
      FactorTrace a target next tail → FactorTrace a target start (start :: tail)

theorem FactorTrace.nonempty {a : Pattern} {target start : Nat} {rows : List Nat}
    (h : FactorTrace a target start rows) : rows ≠ [] := by cases h <;> simp

theorem FactorTrace.target_lt {a : Pattern} {target start : Nat} {rows : List Nat}
    (h : FactorTrace a target start rows) : target < start := by
  induction h with
  | single _ hn => exact hn
  | cons _ hn _ ih => exact ih.trans hn

theorem FactorTrace.toTrace {a : Pattern} {target start : Nat} {rows : List Nat}
    (h : FactorTrace a target start rows) : Trace a target start (rows ++ [target]) := by
  induction h with
  | single hp hn => exact .step hn hp hn .done
  | cons hp hn inner ih => exact .step (inner.target_lt.trans hn) hp hn ih

theorem Trace.factorTrace {a : Pattern} {target start : Nat} {rows : List Nat}
    (h : Trace a target start rows) (hne : target < start) :
    FactorTrace a target start rows.dropLast := by
  induction h with
  | done => exact False.elim ((Nat.lt_irrefl _) hne)
  | @step start next tail ht hp hn inner ih =>
    by_cases smaller : target < next
    · rw [List.dropLast_cons_of_ne_nil inner.nonempty]
      exact .cons hp hn (ih smaller)
    · have same : next = target := le_antisymm (Nat.le_of_not_gt smaller) inner.target_le
      subst next
      have last : tail = [target] := inner.unique .done
      subst tail
      simpa using FactorTrace.single hp hn

/-- Exactly dropping the last entry of the original trace is reversible. -/
theorem factorTrace_iff {a : Pattern} {target start : Nat} {rows : List Nat} :
    FactorTrace a target start rows ↔ Trace a target start (rows ++ [target]) ∧ target < start := by
  constructor
  · exact fun h => ⟨h.toTrace, h.target_lt⟩
  · rintro ⟨h, smaller⟩
    simpa using h.factorTrace smaller

namespace CutAction
variable {S : Type v} {C : CutSpace.{u} S}

def listWord (F : Nat → CutAction C) (rows : List Nat) (nonempty : rows ≠ []) : CutAction C :=
  match rows with
  | [] => False.elim (nonempty rfl)
  | head :: tail => word (F head) (tail.map F)

theorem listWord_single (F : Nat → CutAction C) (r : Nat) :
    listWord F [r] (by simp) = F r := rfl

theorem listWord_cons (F : Nat → CutAction C) (r : Nat) (rows : List Nat) (hne : rows ≠ []) :
    listWord F (r :: rows) (by simp) = (F r).comp (listWord F rows hne) := by
  cases rows with
  | nil => exact False.elim (hne rfl)
  | cons => rfl

/-- Evaluation reads the list from right to left, the usual composition order. -/
def evalList (F : Nat → CutAction C) (rows : List Nat) (z : S) : S :=
  rows.foldr (fun r input => (F r).act input) z

theorem listWord_act (F : Nat → CutAction C) (rows : List Nat) (hne : rows ≠ []) (z : S) :
    (listWord F rows hne).act z = evalList F rows z := by
  induction rows with
  | nil => exact False.elim (hne rfl)
  | cons r rows ih =>
    cases rows with
    | nil => rfl
    | cons s rest =>
      rw [listWord_cons F r (s :: rest) (by simp), comp_act, ih (by simp)]
      rfl

/-- Each call has an input in that factor's saved successor-rank domain. -/
def CallsWithin (F : Nat → CutAction C) (source : Nat → Ordinal.{u}) : List Nat → S → Prop
  | [], _ => True
  | r :: rows, z => CallsWithin F source rows z ∧ C.rank (evalList F rows z) ≤ source r

theorem CallsWithin.cut_at_step {F : Nat → CutAction C} {source : Nat → Ordinal.{u}}
    {r : Nat} {rows : List Nat} {z : S} (h : CallsWithin F source (r :: rows) z) :
    C.cut (source r) (evalList F rows z) = evalList F rows z := C.cut_eq_self h.2

end CutAction

/-- Local facts about actual bounded row actions. Only existing p edges are
tested. No trace-word bound, composite edge or inaccessible image is a field. -/
structure TraceActions (a : Pattern) {S : Type v} (C : CutSpace.{u} S)
    (O : OrdinalView C) (theta : Nat → Ordinal.{u}) where
  action : Nat → CutAction C
  source : Nat → Ordinal.{u}
  bound_eq : ∀ r p, predecessor a r = some p → (action r).bound = theta (r + 1)
  source_image : ∀ r p, predecessor a r = some p → (action r).rho (source r) = (action r).bound
  predecessor_edge : ∀ r p, predecessor a r = some p → (action r).rho (theta p) = theta r
  source_gap : ∀ r p, predecessor a r = some p → theta p < source r
  adjacent_domain : ∀ r p, predecessor a r = some p → theta (p + 1) ≤ source r
  strict_on_source : ∀ r p, predecessor a r = some p →
    StrictMonoOn (action r).rho (Set.Iic (source r))
  ordinal_action : ∀ r p, predecessor a r = some p → ∀ eta,
    (action r).act (O.elem eta) = O.elem ((action r).rho eta)

namespace FactorTrace
variable {a : Pattern} {S : Type v} {C : CutSpace.{u} S} {O : OrdinalView C}
  {theta : Nat → Ordinal.{u}} (D : TraceActions a C O theta)
  {target start : Nat} {rows : List Nat}

def word (h : FactorTrace a target start rows) : CutAction C :=
  CutAction.listWord D.action rows h.nonempty

def inputBound (h : FactorTrace a target start rows) : Ordinal.{u} :=
  D.source (rows.getLast h.nonempty)

theorem word_single {r : Nat} (hp : predecessor a r = some target) (hn : target < r) :
    (FactorTrace.single hp hn).word D = D.action r := rfl

theorem word_cons {r next : Nat} {tail : List Nat} (hp : predecessor a r = some next)
    (hn : next < r) (h : FactorTrace a target next tail) :
    (FactorTrace.cons hp hn h).word D = (D.action r).comp (h.word D) :=
  CutAction.listWord_cons D.action r tail h.nonempty

theorem inputBound_cons {r next : Nat} {tail : List Nat} (hp : predecessor a r = some next)
    (hn : next < r) (h : FactorTrace a target next tail) :
    (FactorTrace.cons hp hn h).inputBound D = h.inputBound D := by
  simp only [inputBound, List.getLast_cons h.nonempty]

/-- The natural top is computed, not assumed: equation (3.12). -/
theorem rho_inputBound (h : FactorTrace a target start rows) :
    (h.word D).rho (h.inputBound D) = (h.word D).bound := by
  induction h with
  | single hp hn => exact D.source_image _ _ hp
  | cons hp hn inner ih =>
    rw [word_cons D hp hn inner, inputBound_cons D hp hn inner,
      CutAction.comp_rho, ih, CutAction.comp_bound]

theorem predecessor_image (h : FactorTrace a target start rows) :
    (h.word D).rho (theta target) = theta start := by
  induction h with
  | single hp hn => exact D.predecessor_edge _ _ hp
  | cons hp hn inner ih =>
    rw [word_cons D hp hn inner, CutAction.comp_rho, ih]
    exact D.predecessor_edge _ _ hp

theorem target_lt_inputBound (h : FactorTrace a target start rows) :
    theta target < h.inputBound D := by
  induction h with
  | single hp hn => exact D.source_gap _ _ hp
  | cons hp hn inner ih => simpa only [inputBound_cons D hp hn inner] using ih

/-- Both inequalities in (3.13), with Delta the actual computed natural top. -/
theorem bound_interval (h : FactorTrace a target start rows) :
    theta start < (h.word D).bound ∧ (h.word D).bound ≤ theta (start + 1) := by
  induction h with
  | @single r hp hn =>
    constructor
    · have strict : (D.action r).rho (theta target) < (D.action r).rho (D.source r) :=
        D.strict_on_source r target hp (D.source_gap r target hp).le
          (show D.source r ≤ D.source r from le_rfl) (D.source_gap r target hp)
      rwa [D.predecessor_edge _ _ hp, D.source_image _ _ hp] at strict
    · exact (D.bound_eq _ _ hp).le
  | @cons r next tail hp hn inner ih =>
    rw [word_cons D hp hn inner, CutAction.comp_bound]
    constructor
    · have innerFits := ih.2.trans (D.adjacent_domain r next hp)
      have strict := D.strict_on_source r next hp (D.source_gap r next hp).le innerFits ih.1
      rwa [D.predecessor_edge r next hp] at strict
    · exact ((D.action r).rho_le_bound _).trans_eq (D.bound_eq r next hp)

theorem strict_on_input (h : FactorTrace a target start rows) :
    StrictMonoOn (h.word D).rho (Set.Iic (h.inputBound D)) := by
  induction h with
  | single hp hn => exact D.strict_on_source _ _ hp
  | @cons r next tail hp hn inner ih =>
    rw [word_cons D hp hn inner, inputBound_cons D hp hn inner]
    intro eta heta zeta hzeta smaller
    have fits : (inner.word D).bound ≤ D.source r :=
      (inner.bound_interval D).2.trans (D.adjacent_domain r next hp)
    exact D.strict_on_source r next hp (((inner.word D).rho_le_bound eta).trans fits)
      (((inner.word D).rho_le_bound zeta).trans fits) (ih heta hzeta smaller)

theorem ordinal_action (h : FactorTrace a target start rows) (eta : Ordinal.{u}) :
    (h.word D).act (O.elem eta) = O.elem ((h.word D).rho eta) := by
  induction h with
  | single hp hn => exact D.ordinal_action _ _ hp eta
  | cons hp hn inner ih =>
    rw [word_cons D hp hn inner, CutAction.comp_act, ih, D.ordinal_action _ _ hp,
      CutAction.comp_rho]

theorem actual_inputBound (h : FactorTrace a target start rows) :
    (h.word D).act (O.elem (h.inputBound D)) = O.elem (h.word D).bound := by
  rw [h.ordinal_action D, h.rho_inputBound D]

theorem actual_predecessor_image (h : FactorTrace a target start rows) :
    (h.word D).act (O.elem (theta target)) = O.elem (theta start) := by
  rw [h.ordinal_action D, h.predecessor_image D]

/-- Every actual intermediate output lies in the next saved domain. -/
theorem callsWithin (h : FactorTrace a target start rows) (z : S)
    (hz : C.rank z ≤ h.inputBound D) : CutAction.CallsWithin D.action D.source rows z := by
  induction h with
  | single hp hn => exact ⟨True.intro, hz⟩
  | @cons r next tail hp hn inner ih =>
    refine ⟨ih (by simpa only [inputBound_cons D hp hn inner] using hz), ?_⟩
    rw [← CutAction.listWord_act D.action tail inner.nonempty]
    exact ((inner.word D).output_rank_le z).trans
      ((inner.bound_interval D).2.trans (D.adjacent_domain r next hp))

/-- An arbitrary internal input is first cut once at the bottom source; all
subsequent calls then use their saved maps without an additional truncation. -/
theorem callsWithin_cut (h : FactorTrace a target start rows) (z : S) :
    CutAction.CallsWithin D.action D.source rows (C.cut (h.inputBound D) z) :=
  h.callsWithin D _ (C.cut_rank_le _ _)

end FactorTrace
end IBLP
