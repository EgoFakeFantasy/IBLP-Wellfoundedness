import IBLP.Syntax

namespace IBLP

/-- 准确 p 输送，列表包括最终配对源。 -/
inductive Trace (a : Pattern) (target : Nat) : Nat → List Nat → Prop
  | done : Trace a target target [target]
  | step {start next : Nat} {tail : List Nat} : target < start →
      predecessor a start = some next → next < start → Trace a target next tail →
      Trace a target start (start :: tail)

def traceFromFuel (a : Pattern) (target : Nat) : Nat → Nat → Option (List Nat)
  | 0, _ => none
  | fuel + 1, start =>
    if start = target then some [start]
    else if target < start then do
      let next ← predecessor a start
      if next < start then
        let tail ← traceFromFuel a target fuel next
        pure (start :: tail)
      else none
    else none

def traceFrom (a : Pattern) (target start : Nat) : Option (List Nat) :=
  traceFromFuel a target (start + 1) start

/-- 标记是否有准确输送只按当前数组与 p 链判定。 -/
def markTrace (a : Pattern) (r b : Nat) : Option (List Nat) := do
  let row ← rowAt a r
  if b ∈ row.columns then
    let k := row.columns.idxOf b
    if row.step ≤ k then
      let target ← row.columns[k - row.step]?
      traceFrom a target b
    else none
  else none

theorem Trace.nonempty {a : Pattern} {target start : Nat} {xs : List Nat}
    (h : Trace a target start xs) : xs ≠ [] := by cases h <;> simp

theorem Trace.head {a : Pattern} {target start : Nat} {xs : List Nat}
    (h : Trace a target start xs) : xs.head? = some start := by cases h <;> rfl

theorem Trace.target_le {a : Pattern} {target start : Nat} {xs : List Nat}
    (h : Trace a target start xs) : target ≤ start := by
  cases h with
  | done => exact le_refl _
  | step ht _ _ _ => exact ht.le

theorem Trace.unique {a : Pattern} {target start : Nat} {xs ys : List Nat}
    (hx : Trace a target start xs) (hy : Trace a target start ys) : xs = ys := by
  induction hx generalizing ys with
  | done =>
    cases hy with
    | done => rfl
    | step h _ _ _ => exact False.elim ((Nat.lt_irrefl _) h)
  | @step start next tail ht hp hn hh ih =>
    cases hy with
    | done => exact False.elim ((Nat.lt_irrefl _) ht)
    | step _ hq _ hy =>
      have same := Option.some.inj (hp.symm.trans hq)
      subst same
      exact congrArg (start :: ·) (ih hy)

theorem traceFromFuel_sound {a : Pattern} {target fuel start : Nat} {xs : List Nat}
    (h : traceFromFuel a target fuel start = some xs) : Trace a target start xs := by
  induction fuel generalizing start xs with
  | zero => simp [traceFromFuel] at h
  | succ fuel ih =>
    simp only [traceFromFuel] at h
    split at h
    · rename_i he
      subst start
      cases h
      exact .done
    · split at h
      · rename_i ht
        cases hp : predecessor a start with
        | none => simp [hp] at h
        | some next =>
          simp only [hp] at h
          dsimp only [Bind.bind, Option.bind] at h
          split at h
          · rename_i hn
            cases hh : traceFromFuel a target fuel next with
            | none => simp [hh] at h
            | some tail =>
              simp only [hh] at h
              dsimp only [Bind.bind, Option.bind, Pure.pure] at h
              simp only [Option.some.injEq] at h
              subst xs
              exact .step ht hp hn (ih hh)
          · simp at h
      · simp at h

theorem Trace.compute {a : Pattern} {target start fuel : Nat} {xs : List Nat}
    (h : Trace a target start xs) (hf : start < fuel) :
    traceFromFuel a target fuel start = some xs := by
  induction h generalizing fuel with
  | done =>
    cases fuel with
    | zero => omega
    | succ fuel => simp [traceFromFuel]
  | @step start next tail ht hp hn h ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hnext : next < fuel := by omega
      simp [traceFromFuel, Nat.ne_of_gt ht, ht, hp, hn, ih hnext]

theorem traceFrom_iff {a : Pattern} {target start : Nat} {xs : List Nat} :
    traceFrom a target start = some xs ↔ Trace a target start xs :=
  ⟨traceFromFuel_sound, fun h => h.compute (Nat.lt_succ_self _)⟩

end IBLP
