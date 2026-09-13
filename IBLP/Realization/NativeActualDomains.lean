import IBLP.NativeEndpoints
import IBLP.Realization.NativeFamilyGraphs

namespace IBLP.FiniteBoundedData
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (D : FiniteBoundedData stage a)
  (r : FiniteRowIndex a) {row : IBLP.Row} {p e : Nat} {sources : List Nat}
  (hr : IBLP.rowAt a r.val = some row) (hp : row.p = some p) (he : row.e = some e)
  (run : IBLP.nativeSources a r.val = some sources)

include D hr hp he run in
theorem nativeBlock_domain {block : IBLP.Pattern}
    (blockRun : IBLP.nativeBlock row r.val sources = some block) (j : Nat) (bound : j ≤ sources.length) :
    (block[j]?).bind IBLP.Row.e = some (nativeDomainIndex r sources j) := by
  simpa only [nativeDomainIndex, rowEndpoint_eq hr he] using
    IBLP.nativeBlock_e D.valid D.shapes hr hp he run blockRun bound

/-- The internal restriction graph is elementary at the source endpoint
read from the actual generated array, not an independently assigned endpoint. -/
theorem nativeFamilyGraph_actual_elementary {block : IBLP.Pattern} {out : IBLP.Row} {endpoint : Nat}
    (blockRun : IBLP.nativeBlock row r.val sources = some block) (j : Nat) (bound : j ≤ sources.length)
    (entry : block[j]? = some out) (atEndpoint : out.e = some endpoint) :
    stage.InternalGraphElementary (D.nativePoint r sources endpoint)
      (D.nativePoint r sources (r.val + j + 1)) (D.nativeFamilyGraph r hr hp he run j) := by
  have actual := D.nativeBlock_domain r hr hp he run blockRun j bound
  rw [entry, Option.bind_some, atEndpoint] at actual
  rw [Option.some.inj actual]
  exact D.nativeFamilyGraph_elementary r hr hp he run j bound

end IBLP.FiniteBoundedData
