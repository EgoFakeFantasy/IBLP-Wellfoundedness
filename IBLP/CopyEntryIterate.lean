import IBLP.CopyEntryTotal
import IBLP.MappedColumns

namespace IBLP

/-- An already copied point always has a next image: low points stay low,
tail points stay in the translated tail, and middle points have a copied
control-row step pair at the same positions. -/
theorem copyEntry_next_exists {n n' minimum minimum' p x fx : Nat} {last next : Row}
    (hm : last.columns.head? = some minimum) (hp : last.p = some p) (included : p ≤ n)
    (hm' : next.columns.head? = some minimum') (hp' : next.p = some n)
    (minimumLe : minimum ≤ minimum') (step : next.step = last.step)
    (mapped : FullMarkedBLP.MapsEntries (copyEntry n last) last.columns next.columns)
    (copied : copyEntry n last x = some fx) : ∃ value, copyEntry n' next fx = some value := by
  rcases copyEntry_cases hm hp copied with ⟨low, equal⟩ | ⟨_, tail, equal⟩ | ⟨_, _, edge⟩
  · subst fx
    exact ⟨x, by simp [copyEntry, hm', hp', show x < minimum' by omega]⟩
  · subst fx
    by_cases low : x + (n - p) < minimum'
    · exact ⟨x + (n - p), by simp [copyEntry, hm', hp', low]⟩
    · exact ⟨x + (n - p) + (n' - n), by simp [copyEntry, hm', hp', low, show n ≤ x + (n - p) by omega]⟩
  · obtain ⟨target, htarget, first, _⟩ := mapped_zip_drop_left mapped last.step edge
    have same : target.1 = fx := Option.some.inj (first.symm.trans copied)
    have pair : (fx, target.2) ∈ next.columns.zip (next.columns.drop next.step) := by
      rw [step, ← same]
      exact htarget
    exact copyEntry_exists_of_edge hm' hp' pair

end IBLP
