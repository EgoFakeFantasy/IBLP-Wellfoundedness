import IBLP.NativeWalk
import FullMarkedBLP.NativeBottomBExact

namespace IBLP

theorem nativeSources_nonempty_first {a : Pattern} {owner p e : Nat} {row : Row} {sources : List Nat}
    (atRow : rowAt a owner = some row) (hp : row.p = some p) (he : row.e = some e)
    (run : nativeSources a owner = some sources) (nonempty : sources ≠ []) :
    row.columns.length ≤ 2 * row.step ∧ ∃ q, penultimate a e = some q ∧ p < q := by
  rcases nativeSources_spec atRow run with ⟨_, empty⟩ | ⟨eligible, actualP, actualE, atP, atE, walk⟩
  · exact False.elim (nonempty empty)
  · have sameP := Option.some.inj (atP.symm.trans hp)
    have sameE := Option.some.inj (atE.symm.trans he)
    subst actualP
    subst actualE
    refine ⟨eligible, ?_⟩
    cases walk with
    | stop => exact False.elim (nonempty rfl)
    | step edge above rest => exact ⟨_, edge, above⟩

/-- A nonempty native record excludes both the long branch and the
two-column middle row; its endpoint is strictly before the owner. -/
theorem nativeSources_nonempty_endpoint_lt {a : Pattern} (valid : BasicValid a) (shapes : OrdinaryShape a)
    {owner e : Nat} {row : Row} {sources : List Nat} (atRow : rowAt a owner = some row)
    (he : row.e = some e) (run : nativeSources a owner = some sources) (nonempty : sources ≠ []) : e < owner := by
  have encodedAt : FullMarkedBLP.rowAt (NativeBridge.encode a) owner = some (NativeBridge.encodeRow row) := by
    simp only [NativeBridge.rowAt_encode, atRow, Option.map_some]
  have encodedRun := (NativeBridge.nativeSources_encode a owner).trans run
  have step := FullMarkedBLP.nativeSources_nonempty_step_ge_two
    (NativeBridge.valid_encode valid shapes _ _ encodedAt) encodedAt encodedRun nonempty
  change 2 ≤ row.step at step
  exact FullMarkedBLP.fromRight_lt_last (valid _ _ atRow).1 (valid _ _ atRow).2.2.1 (by omega) he

end IBLP
