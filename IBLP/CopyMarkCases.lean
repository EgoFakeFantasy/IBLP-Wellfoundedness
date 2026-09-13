import IBLP.Operations

namespace IBLP

/-- Exhaustive origins of every mark actually accepted by the original
copy filter. Missing traces or missing crossing images cannot be accepted. -/
theorem keepCopiedMark_cases {a : Pattern} {last row : Row} {cols : List Nat}
    {r mark minimum p : Nat} (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (kept : keepCopiedMark a last r row cols mark = true) :
    ∃ trace bottom, markTrace a r mark = some trace ∧ fromRight trace 2 = some bottom ∧
      (p ≤ bottom ∨ (bottom < p ∧ ∃ boundary, trace.find? (· < p) = some boundary ∧
        (boundary < minimum ∨ (minimum ≤ boundary ∧ ∃ image, copyEntry a.length last boundary = some image)))) := by
  cases computed : markTrace a r mark with
  | none => simp [keepCopiedMark, hm, hp, computed] at kept
  | some trace =>
    cases bottomAt : fromRight trace 2 with
    | none => simp [keepCopiedMark, hm, hp, computed, bottomAt] at kept
    | some bottom =>
      refine ⟨trace, bottom, rfl, bottomAt, ?_⟩
      by_cases full : p ≤ bottom
      · exact Or.inl full
      · refine Or.inr ⟨by omega, ?_⟩
        cases found : trace.find? (· < p) with
        | none => simp [keepCopiedMark, hm, hp, computed, bottomAt, full, found] at kept
        | some boundary =>
          refine ⟨boundary, rfl, ?_⟩
          by_cases low : boundary < minimum
          · exact Or.inl low
          · refine Or.inr ⟨by omega, ?_⟩
            cases image : copyEntry a.length last boundary with
            | none => simp [keepCopiedMark, hm, hp, computed, bottomAt, full, found, low, image] at kept
            | some value => exact ⟨value, rfl⟩

end IBLP
