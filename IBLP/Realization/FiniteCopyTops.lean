import IBLP.Realization.FiniteCopiesRealized
import IBLP.Realization.RawCopyPointsExact
import IBLP.Realization.CutRealized
import IBLP.RawCopiesLength

namespace IBLP.MarkedRealization
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (R : MarkedRealization stage a)

/-- The same copied certificate simultaneously tracks the implicit top and
the last explicit point, which becomes the top after cut. -/
theorem rawCopy_realization_exact_exists {b : IBLP.Pattern} (copy : IBLP.rawCopy a = some b) :
    ∃ next : ModelStage.{u}, ∃ j : stage.model.ElementaryMap next.model, ∃ S : MarkedRealization next b,
      S.top = stage.ordinalImage j R.top ∧
      S.data.point b.length = stage.ordinalImage j (R.data.point a.length) ∧
      next.model.carrier ⊆ stage.model.carrier := by
  obtain ⟨last, p, _, hlast, hp, positive, included, _, _⟩ := IBLP.rawCopy_decomposition copy
  have nonempty : 0 < a.length := by omega
  have valid := R.data.valid _ _ (IBLP.getLast_rowAt hlast)
  have first : 0 < last.columns.length := by have := valid.2.1; omega
  let minimum := last.columns[0]
  have hm : last.columns.head? = some minimum := by
    rw [List.head?_eq_getElem?]
    exact List.getElem?_eq_some_iff.mpr ⟨first, rfl⟩
  exact ⟨(R.data.lastExtension nonempty).next, (R.data.lastExtension nonempty).embedding,
    R.rawCopy nonempty copy hlast hm hp, R.rawCopy_top nonempty copy hlast hm hp,
    R.data.rawCopyData_lastPoint nonempty R.proper copy hlast hm hp, (R.data.lastExtension nonempty).inside⟩

theorem rawCopies_realization_exact_exists (m : Nat) {b : IBLP.Pattern} (run : IBLP.rawCopies m a = some b) :
    ∃ next : ModelStage.{u}, ∃ j : stage.model.ElementaryMap next.model, ∃ S : MarkedRealization next b,
      S.top = stage.ordinalImage j R.top ∧
      S.data.point b.length = stage.ordinalImage j (R.data.point a.length) ∧
      next.model.carrier ⊆ stage.model.carrier := by
  induction m generalizing stage a b with
  | zero =>
    have same : a = b := Option.some.inj run
    subst b
    exact ⟨stage, FirstOrder.Language.ElementaryEmbedding.refl membershipLanguage stage.model.Element,
      R, (stage.ordinalImage_refl R.top).symm,
      (stage.ordinalImage_refl (R.data.point a.length)).symm, fun _ member => member⟩
  | succ m ih =>
    obtain ⟨middlePattern, copy, rest⟩ := Option.bind_eq_some_iff.mp run
    obtain ⟨middle, j, S, top, last, inside⟩ := R.rawCopy_realization_exact_exists copy
    obtain ⟨next, k, T, top', last', inside'⟩ := ih S rest
    refine ⟨next, k.comp j, T, ?_, ?_, fun _ member => inside (inside' member)⟩
    · exact top'.trans ((congrArg (middle.ordinalImage k) top).trans
        (stage.ordinalImage_comp middle next j k R.top).symm)
    · exact last'.trans ((congrArg (middle.ordinalImage k) last).trans
        (stage.ordinalImage_comp middle next j k (R.data.point a.length)).symm)

/-- Manuscript (8.1), before the frozen scan: every finite copying phase and
its actual cut are defined, all marks are realized, and the top is exactly
the image of the parent's last explicit point, strictly below the image of
the old top. No saturation of the intermediate copied pattern is assumed. -/
theorem copies_cut_realization_exists (first : ∃ b, IBLP.rawCopy a = some b) (m : Nat) :
    ∃ b c, IBLP.rawCopies m a = some b ∧ IBLP.cut b = some c ∧
      ∃ next : ModelStage.{u}, ∃ j : stage.model.ElementaryMap next.model, ∃ S : MarkedRealization next c,
        S.top = stage.ordinalImage j (R.data.point a.length) ∧
        S.top < stage.ordinalImage j R.top ∧ next.model.carrier ⊆ stage.model.carrier := by
  obtain ⟨firstPattern, firstRun⟩ := first
  obtain ⟨_, _, _, _, _, positive, included, _⟩ := IBLP.rawCopy_decomposition firstRun
  have nonempty : 0 < a.length := by omega
  obtain ⟨b, run⟩ := R.data.rawCopies_exists R.proper ⟨firstPattern, firstRun⟩ m
  obtain ⟨next, j, S, top, last, inside⟩ := R.rawCopies_realization_exact_exists m run
  have cutRun := IBLP.cut_defined (nonempty.trans_le (IBLP.rawCopies_length_le run))
  obtain ⟨T, newTop, smaller⟩ := S.cut_realization_exists cutRun
  exact ⟨b, b.take (b.length - 1), run, cutRun, next, j, T,
    newTop.trans last, top ▸ smaller, inside⟩

end IBLP.MarkedRealization
