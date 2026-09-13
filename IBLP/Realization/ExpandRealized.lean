import IBLP.Realization.CopyScanRealized
import IBLP.Realization.FiniteCopyTops

namespace IBLP.BoundedRealization
open FullMarkedBLP
universe u

theorem cut_image_realization {stage : ModelStage.{u}} {a b : IBLP.Pattern}
    (R : BoundedRealization stage a) (run : IBLP.cut a = some b) :
    ∃ next : ModelStage.{u}, ∃ j : stage.model.ElementaryMap next.model,
      ∃ S : BoundedRealization next b,
        S.top = stage.ordinalImage j (R.data.point a.length) ∧
        S.top < stage.ordinalImage j R.top ∧ next.model.carrier ⊆ stage.model.carrier := by
  obtain ⟨S, top, smaller⟩ := R.cut_realization_exists run
  refine ⟨stage, FirstOrder.Language.ElementaryEmbedding.refl membershipLanguage stage.model.Element,
    S, ?_, ?_, fun _ member => member⟩
  · simpa only [stage.ordinalImage_refl] using top
  · simpa only [stage.ordinalImage_refl] using smaller

/-- Complete manuscript (8.1) for the actual original expand operation,
including its first-copy fallback, original frozen scan, and every final
saturation and weak-mark condition. The child top is exactly the image of
the parent's last explicit point, strictly below the image of its top. -/
theorem expand_realization {stage : ModelStage.{u}} {a b : IBLP.Pattern}
    (R : BoundedRealization stage a) {m : Nat} (run : IBLP.expand a m = some b) :
    ∃ next : ModelStage.{u}, ∃ j : stage.model.ElementaryMap next.model,
      ∃ S : BoundedRealization next b,
        S.top = stage.ordinalImage j (R.data.point a.length) ∧
        S.top < stage.ordinalImage j R.top ∧ next.model.carrier ⊆ stage.model.carrier := by
  unfold IBLP.expand at run
  split at run
  · simp at run
  · split at run
    · exact R.cut_image_realization run
    · rename_i notSimple
      cases firstRun : IBLP.rawCopy a with
      | none =>
        simp only [firstRun] at run
        exact R.cut_image_realization run
      | some first =>
        simp only [firstRun] at run
        obtain ⟨copied, copies, run⟩ := Option.bind_eq_some_iff.mp run
        obtain ⟨initial, cut, scan⟩ := Option.bind_eq_some_iff.mp run
        have nonzero : m ≠ 0 := fun zero => notSimple (Or.inl zero)
        have fullCopies : IBLP.rawCopies m a = some copied := by
          calc
            IBLP.rawCopies m a = IBLP.rawCopies ((m - 1) + 1) a := by congr 1; omega
            _ = some copied := by simp only [IBLP.rawCopies, firstRun, Option.bind_some, copies]
        obtain ⟨last, p, _, atLast, hp, _, _, _⟩ := IBLP.rawCopy_decomposition firstRun
        obtain ⟨next, j, copiedRealization, copiedTop, lastPoint, inside⟩ :=
          R.toMarkedRealization.rawCopies_realization_exact_exists m fullCopies
        obtain ⟨entry, cutTop, cutSmaller⟩ := copiedRealization.cut_realization_exists cut
        obtain ⟨S, scanTop⟩ := R.copies_scan_realized entry atLast hp fullCopies cut scan
        exact ⟨next, j, S, scanTop.trans (cutTop.trans lastPoint),
          scanTop ▸ copiedTop ▸ cutSmaller, inside⟩

end IBLP.BoundedRealization
