import IBLP.Realization.RawCopyGraphExact
import IBLP.Realization.TraceGraphCongruence
import IBLP.Realization.MarkGraphCongruence
import IBLP.Realization.MarkImage

namespace IBLP.FiniteBoundedData
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (D : FiniteBoundedData stage a)

/-- Every factor graph in a fully copied history is its actual elementary
image, so the entire composite graph is also that image. -/
theorem fullCopy_traceGraph (nonempty : 0 < a.length) {b : IBLP.Pattern} {last : IBLP.Row}
    {minimum p target start target' start' : Nat} {rows : List Nat}
    (proper : IBLP.ProperMarks a) (copy : IBLP.rawCopy a = some b)
    (hlast : a.getLast? = some last) (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (h : FactorTrace a target start rows)
    (h' : FactorTrace b target' start' (rows.map (· + (a.length - p))))
    (tail : ∀ r ∈ rows, p ≤ r) :
    (D.rawCopyData nonempty proper copy hlast hm hp).traceGraph h' =
      (D.lastExtension nonempty).embedding (D.traceGraph h) := by
  let image := D.image (D.lastExtension nonempty).next (D.lastExtension nonempty).embedding
  let copied := D.rawCopyData nonempty proper copy hlast hm hp
  have matched : List.Forall₂ (image.RowGraphsEqual copied) rows (rows.map (· + (a.length - p))) := by
    have build (xs : List Nat) (pointwise : ∀ r ∈ xs, image.RowGraphsEqual copied r (r + (a.length - p))) :
        List.Forall₂ (image.RowGraphsEqual copied) xs (xs.map (· + (a.length - p))) := by
      induction xs with
      | nil => constructor
      | cons r rs ih =>
        exact .cons (pointwise r (by simp)) (ih (fun t ht => pointwise t (List.mem_cons_of_mem r ht)))
    apply build
    intro r hr oldValid newValid
    have pr := tail r hr
    exact (D.rawCopyData_graph_new nonempty proper copy hlast hm hp
      ⟨r + (a.length - p), newValid⟩ ⟨r, oldValid⟩ (by dsimp; omega) rfl).symm
  exact (image.traceGraph_congr_rows copied h h' matched).symm.trans
    (D.traceGraph_image (D.lastExtension nonempty).next (D.lastExtension nonempty).embedding h)

/-- Full copying transports weak equality on every input in its natural
bound. The proof uses the finite formula for the complete carrier and trace
graphs, rather than restricting inputs to the range of the embedding. -/
theorem fullCopy_markCertificate (nonempty : 0 < a.length) {b : IBLP.Pattern} {last : IBLP.Row}
    {minimum p target start target' start' : Nat} {rows : List Nat}
    (proper : IBLP.ProperMarks a) (copy : IBLP.rawCopy a = some b)
    (hlast : a.getLast? = some last) (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (r : FiniteRowIndex a) (s : FiniteRowIndex b) (carrierTail : p ≤ r.val)
    (owner : s.val = r.val + (a.length - p))
    (h : FactorTrace a target start rows)
    (h' : FactorTrace b target' start' (rows.map (· + (a.length - p))))
    (tail : ∀ r ∈ rows, p ≤ r) :
    h'.MarkCertificate (D.rawCopyData nonempty proper copy hlast hm hp).toFiniteTraceRows.toInternalTraceRows s.val ↔
      h.MarkCertificate D.toFiniteTraceRows.toInternalTraceRows r.val := by
  let image := D.image (D.lastExtension nonempty).next (D.lastExtension nonempty).embedding
  let copied := D.rawCopyData nonempty proper copy hlast hm hp
  have carrier : image.graph r = copied.graph s :=
    (D.rawCopyData_graph_new nonempty proper copy hlast hm hp s r (by have := r.property.2; omega) owner).symm
  have history : image.traceGraph h = copied.traceGraph h' :=
    (D.traceGraph_image (D.lastExtension nonempty).next (D.lastExtension nonempty).embedding h).trans
      (D.fullCopy_traceGraph nonempty proper copy hlast hm hp h h' tail).symm
  exact (image.markCertificate_congr_graphs copied r s h h' carrier history).symm.trans
    (D.markCertificate_image (D.lastExtension nonempty).next (D.lastExtension nonempty).embedding r h)

end IBLP.FiniteBoundedData
