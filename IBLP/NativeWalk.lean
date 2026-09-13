import IBLP.NativeTotal

namespace IBLP

/-- The actual decreasing q staircase and its final stopping test. The
record is stored in descending order exactly as nativeSources returns it. -/
inductive NativeWalk (a : Pattern) (p : Nat) : Nat → List Nat → Prop
  | stop {u q} : penultimate a u = some q → q ≤ p → NativeWalk a p u []
  | step {u q tail} : penultimate a u = some q → p < q → NativeWalk a p q tail → NativeWalk a p u (q :: tail)

theorem nativeSourcesFuel_walk {a : Pattern} {p fuel u : Nat} {sources : List Nat}
    (run : nativeSourcesFuel a p fuel u = some sources) : NativeWalk a p u sources := by
  induction fuel generalizing u sources with
  | zero => simp [nativeSourcesFuel] at run
  | succ fuel ih =>
    obtain ⟨q, atQ, run⟩ := Option.bind_eq_some_iff.mp run
    split at run
    · rename_i above
      obtain ⟨tail, rest, run⟩ := Option.bind_eq_some_iff.mp run
      cases Option.some.inj run
      exact .step atQ above (ih rest)
    · rename_i below
      cases Option.some.inj run
      exact .stop atQ (by omega)

theorem nativeSources_spec {a : Pattern} {r : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (run : nativeSources a r = some sources) :
    (2 * row.step < row.columns.length ∧ sources = []) ∨
      (row.columns.length ≤ 2 * row.step ∧ ∃ p e, row.p = some p ∧ row.e = some e ∧ NativeWalk a p e sources) := by
  unfold nativeSources at run
  rw [hr] at run
  dsimp only [Bind.bind, Option.bind] at run
  split at run
  · rename_i long
    exact Or.inl ⟨long, (Option.some.inj run).symm⟩
  · rename_i short
    obtain ⟨p, hp, run⟩ := Option.bind_eq_some_iff.mp run
    obtain ⟨e, he, run⟩ := Option.bind_eq_some_iff.mp run
    exact Or.inr ⟨by omega, p, e, hp, he, nativeSourcesFuel_walk run⟩

namespace NativeWalk

theorem bounds {a : Pattern} (valid : BasicValid a) {p u : Nat} {sources : List Nat}
    (h : NativeWalk a p u sources) : ∀ s ∈ sources, p < s ∧ s < u := by
  induction h with
  | stop => simp
  | @step u q tail edge above rest ih =>
    intro s member
    have lower := penultimate_lt valid edge
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨above, lower⟩
    · exact ⟨(ih s member).1, (ih s member).2.trans lower⟩

theorem last_stop {a : Pattern} {p u : Nat} {sources : List Nat}
    (h : NativeWalk a p u sources) : ∃ q, penultimate a (sources.getLast?.getD u) = some q ∧ q ≤ p := by
  induction h with
  | stop edge below => exact ⟨_, edge, below⟩
  | @step u q tail edge above rest ih =>
    cases tail with
    | nil => exact ih
    | cons t ts => simpa using ih

end NativeWalk

theorem nativeSources_bounds {a : Pattern} (valid : BasicValid a) {r p e : Nat}
    {row : Row} {sources : List Nat} (hr : rowAt a r = some row) (hp : row.p = some p)
    (he : row.e = some e) (run : nativeSources a r = some sources) :
    ∀ s ∈ sources, p < s ∧ s < e := by
  rcases nativeSources_spec hr run with ⟨_, empty⟩ | ⟨_, p', e', hp', he', walk⟩
  · simp [empty]
  · have sameP : p' = p := Option.some.inj (hp'.symm.trans hp)
    have sameE : e' = e := Option.some.inj (he'.symm.trans he)
    subst p'
    subst e'
    exact walk.bounds valid

end IBLP
