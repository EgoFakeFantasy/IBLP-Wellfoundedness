import IBLP.Realization.HighInnerBounds
import IBLP.Realization.TraceWordPieces
import IBLP.Extender.HighCrossingAgreement
import IBLP.Realization.LowSuffixAgreement

namespace IBLP.FiniteBoundedData
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (D : FiniteBoundedData stage a)

/-- High-crossing weak equality at the computed new natural bound. The
two inner estimates are proved here from the actual control certificate;
the row-edge input estimate is supplied by HighInputBound. -/
theorem highCopy_markCertificate (nonempty : 0 < a.length) {b : IBLP.Pattern} {last : IBLP.Row}
    {minimum p target start boundary imageBoundary imageStart : Nat} {front bridge suffix : List Nat}
    (proper : IBLP.ProperMarks a) (copy : IBLP.rawCopy a = some b)
    (hlast : a.getLast? = some last) (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (r : FiniteRowIndex a) (s : FiniteRowIndex b) (carrierTail : p ≤ r.val)
    (owner : s.val = r.val + (a.length - p))
    (before : FactorPrefix a boundary start front) (after : FactorTrace a target boundary suffix)
    (tail : ∀ r ∈ front, p ≤ r) (control : FactorTrace a boundary imageBoundary bridge)
    (old : imageBoundary < a.length)
    (newBefore : FactorPrefix b imageBoundary imageStart (front.map (· + (a.length - p))))
    (certificate : (before.appendTrace after).MarkCertificate D.toFiniteTraceRows.toInternalTraceRows r.val)
    (controlCertificate : control.MarkCertificate D.toFiniteTraceRows.toInternalTraceRows a.length)
    (inputBound : ∀ {rows} (h : FactorTrace b target imageStart rows),
      (h.word (D.rawCopyData nonempty proper copy hlast hm hp).toFiniteTraceRows.toInternalTraceRows.actions).bound ≤
        ((D.rawCopyData nonempty proper copy hlast hm hp).toFiniteTraceRows.toInternalTraceRows.actions.action s.val).rho
          (D.point minimum)) :
    (newBefore.appendTrace ((IBLP.rawCopy_factorTrace_old copy control old).append
      (IBLP.rawCopy_factorTrace_old copy after (control.target_lt.trans old)))).MarkCertificate
      (D.rawCopyData nonempty proper copy hlast hm hp).toFiniteTraceRows.toInternalTraceRows s.val := by
  let copied := D.rawCopyData nonempty proper copy hlast hm hp
  let original := D.toFiniteTraceRows.toInternalTraceRows
  let current := copied.toFiniteTraceRows.toInternalTraceRows
  let retainedT := IBLP.rawCopy_factorTrace_old copy control old
  let retainedV := IBLP.rawCopy_factorTrace_old copy after (control.target_lt.trans old)
  have lastAt := IBLP.getLast_rowAt hlast
  have critical := D.critical (lastIndex nonempty) last minimum lastAt hm
  have criticalBound := D.criticalPoint_le_source (lastIndex nonempty) lastAt hm
  have allInputs := ((before.appendTrace after).markCertificate_iff_allInputs original r.val).mp certificate
  have controlInputs := (control.markCertificate_iff_allInputs original a.length).mp controlCertificate
  rw [D.lastAction_eq nonempty] at controlInputs
  have imageF := D.rawCopy_rowAction_image nonempty proper copy hlast hm hp r s carrierTail owner
  have innerBounds := D.highCopy_inner_bounds nonempty proper copy hlast hm hp control after old controlCertificate
  have retainT := D.rawCopy_traceAction_old nonempty proper copy hlast hm hp control old
  have retainV := D.rawCopy_traceAction_old nonempty proper copy hlast hm hp after (control.target_lt.trans old)
  by_cases empty : front = []
  · subst front
    cases before
    cases newBefore
    have input := inputBound (retainedT.append retainedV)
    rw [retainedT.word_append current.actions retainedV] at input
    have agreement := (D.lastExtension nonempty).high_crossing_no_front
      (D.point_limit (rowEndpoint a a.length)) (D.point minimum) criticalBound critical (D.traceBound_le_top control)
      allInputs imageF controlInputs retainT retainV input innerBounds.1 innerBounds.2
    change CutAction.WeakAgreement (current.actions.action s.val)
      ((retainedT.append retainedV).word current.actions) ((retainedT.append retainedV).word current.actions).bound
    rw [retainedT.word_append current.actions retainedV]
    exact agreement.weak
  · let upper := before.toFactorTrace empty
    let upper' := newBefore.toFactorTrace (by simpa using empty)
    have imageU := D.rawCopy_traceAction_image nonempty proper copy hlast hm hp upper upper' tail
    change CutAction.AllInputAgreement (original.actions.action r.val)
      ((upper.append after).word original.actions) ((upper.append after).word original.actions).bound at allInputs
    rw [upper.word_append original.actions after] at allInputs
    have input := inputBound (upper'.append (retainedT.append retainedV))
    rw [upper'.word_append current.actions (retainedT.append retainedV),
      retainedT.word_append current.actions retainedV] at input
    have imageBound : ((upper'.word current.actions).comp
        ((retainedT.word current.actions).comp (retainedV.word current.actions))).bound ≤
        stage.ordinalImage (D.lastExtension nonempty).embedding
          ((upper.word original.actions).comp (after.word original.actions)).bound :=
      ((upper'.word current.actions).monotone innerBounds.1).trans_eq
        (imageU.rho (after.word original.actions).bound)
    have bridgeBound := (upper'.word current.actions).monotone innerBounds.2
    have agreement := (D.lastExtension nonempty).high_crossing_allInputs
      (D.point_limit (rowEndpoint a a.length)) (D.point minimum) criticalBound critical (D.traceBound_le_top control)
      allInputs imageF imageU controlInputs retainT retainV input imageBound bridgeBound
    change CutAction.WeakAgreement (current.actions.action s.val)
      ((upper'.append (retainedT.append retainedV)).word current.actions)
      ((upper'.append (retainedT.append retainedV)).word current.actions).bound
    rw [upper'.word_append current.actions (retainedT.append retainedV), retainedT.word_append current.actions retainedV]
    exact agreement.weak

end IBLP.FiniteBoundedData
