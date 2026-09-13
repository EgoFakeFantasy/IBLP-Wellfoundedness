import IBLP.Realization.RawCopyRealized
import IBLP.Realization.NextCopy
import IBLP.Model.OrdinalImageComposition

namespace IBLP.MarkedRealization
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (R : MarkedRealization stage a)

/-- A successful raw copy supplies every piece of its semantic certificate
without requiring separately supplied control-row metadata. -/
theorem rawCopy_realization_exists {b : IBLP.Pattern} (copy : IBLP.rawCopy a = some b) :
    ∃ next : ModelStage.{u}, ∃ j : stage.model.ElementaryMap next.model, ∃ S : MarkedRealization next b,
      S.top = stage.ordinalImage j R.top ∧ next.model.carrier ⊆ stage.model.carrier := by
  obtain ⟨last, p, _, hlast, hp, positive, included, _, _⟩ := IBLP.rawCopy_decomposition copy
  have nonempty : 0 < a.length := by omega
  have valid := R.data.valid _ _ (IBLP.getLast_rowAt hlast)
  have first : 0 < last.columns.length := by have := valid.2.1; omega
  let minimum := last.columns[0]
  have hm : last.columns.head? = some minimum := by
    rw [List.head?_eq_getElem?]
    exact List.getElem?_eq_some_iff.mpr ⟨first, rfl⟩
  exact ⟨(R.data.lastExtension nonempty).next, (R.data.lastExtension nonempty).embedding,
    R.rawCopy nonempty copy hlast hm hp, R.rawCopy_top nonempty copy hlast hm hp, (R.data.lastExtension nonempty).inside⟩

/-- Every actual finite sequence of original raw copies has all mark
certificates in a genuine iterated target model. Its top is the image under
the composite elementary embedding, and the target remains inside the source. -/
theorem rawCopies_realization_exists (m : Nat) {b : IBLP.Pattern} (run : IBLP.rawCopies m a = some b) :
    ∃ next : ModelStage.{u}, ∃ j : stage.model.ElementaryMap next.model, ∃ S : MarkedRealization next b,
      S.top = stage.ordinalImage j R.top ∧ next.model.carrier ⊆ stage.model.carrier := by
  induction m generalizing stage a b with
  | zero =>
    have same : a = b := Option.some.inj run
    subst b
    exact ⟨stage, FirstOrder.Language.ElementaryEmbedding.refl membershipLanguage stage.model.Element,
      R, (stage.ordinalImage_refl R.top).symm, fun _ member => member⟩
  | succ m ih =>
    obtain ⟨middlePattern, copy, rest⟩ := Option.bind_eq_some_iff.mp run
    obtain ⟨middle, j, S, top, inside⟩ := R.rawCopy_realization_exists copy
    obtain ⟨next, k, T, top', inside'⟩ := ih S rest
    refine ⟨next, k.comp j, T, ?_, fun _ member => inside (inside' member)⟩
    exact top'.trans ((congrArg (middle.ordinalImage k) top).trans
      (stage.ordinalImage_comp middle next j k R.top).symm)

theorem rawCopies_all_realized (first : ∃ b, IBLP.rawCopy a = some b) (m : Nat) :
    ∃ b, IBLP.rawCopies m a = some b ∧
      ∃ next : ModelStage.{u}, ∃ j : stage.model.ElementaryMap next.model, ∃ S : MarkedRealization next b,
        S.top = stage.ordinalImage j R.top ∧ next.model.carrier ⊆ stage.model.carrier := by
  obtain ⟨b, run⟩ := R.data.rawCopies_exists R.proper first m
  exact ⟨b, run, R.rawCopies_realization_exists m run⟩

end IBLP.MarkedRealization
