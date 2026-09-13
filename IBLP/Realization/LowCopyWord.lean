import IBLP.Realization.LowSuffixAgreement
import IBLP.Realization.TraceWordPieces

namespace IBLP.FiniteBoundedData
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (D : FiniteBoundedData stage a)

/-- The low-crossing replacement has no larger natural bound than the
image word and agrees with it throughout that new bound. Empty initial
segments are handled directly, without inventing an empty bounded word. -/
theorem lowCopy_wordAgreement (nonempty : 0 < a.length) {b : IBLP.Pattern} {last : IBLP.Row}
    {minimum p target start boundary imageStart : Nat} {front suffix : List Nat}
    (proper : IBLP.ProperMarks a) (copy : IBLP.rawCopy a = some b)
    (hlast : a.getLast? = some last) (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (before : FactorPrefix a boundary start front) (after : FactorTrace a target boundary suffix)
    (tail : ∀ r ∈ front, p ≤ r) (low : boundary < minimum) (old : boundary < a.length)
    (newBefore : FactorPrefix b boundary imageStart (front.map (· + (a.length - p)))) :
    let image := D.image (D.lastExtension nonempty).next (D.lastExtension nonempty).embedding
    let copied := D.rawCopyData nonempty proper copy hlast hm hp
    let oldWord := (before.appendTrace after).word image.toFiniteTraceRows.toInternalTraceRows.actions
    let newWord := (newBefore.appendTrace (IBLP.rawCopy_factorTrace_old copy after old)).word
      copied.toFiniteTraceRows.toInternalTraceRows.actions
    newWord.bound ≤ oldWord.bound ∧ CutAction.AllInputAgreement oldWord newWord newWord.bound := by
  let image := D.image (D.lastExtension nonempty).next (D.lastExtension nonempty).embedding
  let copied := D.rawCopyData nonempty proper copy hlast hm hp
  let retained := IBLP.rawCopy_factorTrace_old copy after old
  have retainedBound := D.rawCopy_traceBounds_old nonempty proper copy hlast hm hp after old
  have suffixLower : (retained.word copied.toFiniteTraceRows.toInternalTraceRows.actions).bound ≤
      (after.word image.toFiniteTraceRows.toInternalTraceRows.actions).bound := by
    rw [← retainedBound, D.traceBound_image]
    exact stage.ordinalImage_le (D.lastExtension nonempty).embedding _
  have suffixAgreement := D.lowSuffix_allInputs nonempty proper copy hlast hm hp after low old
  rw [retainedBound] at suffixAgreement
  by_cases empty : front = []
  · subst front
    cases before
    cases newBefore
    exact ⟨suffixLower, suffixAgreement⟩
  · let upper := before.toFactorTrace empty
    let upper' := newBefore.toFactorTrace (by simpa using empty)
    have graphs : image.traceGraph upper = copied.traceGraph upper' :=
      (D.traceGraph_image (D.lastExtension nonempty).next (D.lastExtension nonempty).embedding upper).trans
        (D.fullCopy_traceGraph nonempty proper copy hlast hm hp upper upper' tail).symm
    have actions := image.traceAction_congr_graphs copied upper upper' graphs
    change ((upper'.append retained).word copied.toFiniteTraceRows.toInternalTraceRows.actions).bound ≤
        ((upper.append after).word image.toFiniteTraceRows.toInternalTraceRows.actions).bound ∧
      CutAction.AllInputAgreement ((upper.append after).word image.toFiniteTraceRows.toInternalTraceRows.actions)
        ((upper'.append retained).word copied.toFiniteTraceRows.toInternalTraceRows.actions)
        ((upper'.append retained).word copied.toFiniteTraceRows.toInternalTraceRows.actions).bound
    rw [upper.word_append image.toFiniteTraceRows.toInternalTraceRows.actions after,
      upper'.word_append copied.toFiniteTraceRows.toInternalTraceRows.actions retained, ← actions]
    exact ⟨(upper.word image.toFiniteTraceRows.toInternalTraceRows.actions).monotone suffixLower,
      suffixAgreement.comp_left (upper.word image.toFiniteTraceRows.toInternalTraceRows.actions)⟩

end IBLP.FiniteBoundedData
