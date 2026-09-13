import IBLP.Realization.LowCopyWord
import IBLP.Rank.AgreementReplacement

namespace IBLP.FiniteBoundedData
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (D : FiniteBoundedData stage a)

theorem lowCopy_markCertificate (nonempty : 0 < a.length) {b : IBLP.Pattern} {last : IBLP.Row}
    {minimum p target start boundary imageStart : Nat} {front suffix : List Nat}
    (proper : IBLP.ProperMarks a) (copy : IBLP.rawCopy a = some b)
    (hlast : a.getLast? = some last) (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (r : FiniteRowIndex a) (s : FiniteRowIndex b) (carrierTail : p ≤ r.val)
    (owner : s.val = r.val + (a.length - p))
    (before : FactorPrefix a boundary start front) (after : FactorTrace a target boundary suffix)
    (tail : ∀ r ∈ front, p ≤ r) (low : boundary < minimum) (old : boundary < a.length)
    (newBefore : FactorPrefix b boundary imageStart (front.map (· + (a.length - p))))
    (certificate : (before.appendTrace after).MarkCertificate D.toFiniteTraceRows.toInternalTraceRows r.val) :
    (newBefore.appendTrace (IBLP.rawCopy_factorTrace_old copy after old)).MarkCertificate
      (D.rawCopyData nonempty proper copy hlast hm hp).toFiniteTraceRows.toInternalTraceRows s.val := by
  let image := D.image (D.lastExtension nonempty).next (D.lastExtension nonempty).embedding
  let copied := D.rawCopyData nonempty proper copy hlast hm hp
  let history := before.appendTrace after
  have imageCertificate := (D.markCertificate_image (D.lastExtension nonempty).next
    (D.lastExtension nonempty).embedding r history).mpr certificate
  have allInputs := (history.markCertificate_iff_allInputs image.toFiniteTraceRows.toInternalTraceRows r.val).mp imageCertificate
  obtain ⟨bound, replacement⟩ := D.lowCopy_wordAgreement nonempty proper copy hlast hm hp before after tail low old newBefore
  have transferred := allInputs.replace_word replacement bound
  have graphs : image.graph r = copied.graph s :=
    (D.rawCopyData_graph_new nonempty proper copy hlast hm hp s r (by have := r.property.2; omega) owner).symm
  have actions := image.rowAction_congr_graphs copied r s graphs
  rw [actions] at transferred
  exact transferred.weak

end IBLP.FiniteBoundedData
