import IBLP.Realization.NativePoints
import IBLP.CopyEntry

namespace IBLP.FiniteBoundedData
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (D : FiniteBoundedData stage a)

/-- Source endpoint of family row r+j. For j<h it is the next ascending
record source; the top family row keeps the original source endpoint. -/
def nativeDomainIndex (r : FiniteRowIndex a) (sources : List Nat) (j : Nat) : Nat :=
  if j < sources.length then sources.reverse[j]?.getD 0 else rowEndpoint a r.val

include D in
theorem nativeDomainIndex_le (r : FiniteRowIndex a) {row : IBLP.Row} {p e : Nat} {sources : List Nat}
    (hr : IBLP.rowAt a r.val = some row) (hp : row.p = some p) (he : row.e = some e)
    (run : IBLP.nativeSources a r.val = some sources) (j : Nat) :
    nativeDomainIndex r sources j ≤ rowEndpoint a r.val := by
  unfold nativeDomainIndex
  split
  · rename_i bound
    have reverseBound : j < sources.reverse.length := by simpa using bound
    have member : sources.reverse[j] ∈ sources := List.mem_reverse.mp (List.getElem_mem reverseBound)
    have bounds := IBLP.nativeSources_bounds D.valid hr hp he run _ member
    simp only [List.getElem?_eq_getElem reverseBound, Option.getD_some, rowEndpoint_eq hr he]
    exact bounds.2.le
  · rfl

include D in
theorem nativeDomainIndex_above_minimum (r : FiniteRowIndex a) {row : IBLP.Row} {p e c : Nat} {sources : List Nat}
    (hr : IBLP.rowAt a r.val = some row) (hp : row.p = some p) (he : row.e = some e)
    (hm : row.columns.head? = some c) (run : IBLP.nativeSources a r.val = some sources) (j : Nat) :
    c ≤ nativeDomainIndex r sources j := by
  have minimum := Row.minimum_le_column (D.valid _ _ hr) hm (IBLP.fromRight_mem hp)
  have pred := Row.predecessor_lt_endpoint (D.valid _ _ hr) hp he
  unfold nativeDomainIndex
  split
  · rename_i bound
    have reverseBound : j < sources.reverse.length := by simpa using bound
    have bounds := IBLP.nativeSources_bounds D.valid hr hp he run _
      (List.mem_reverse.mp (List.getElem_mem reverseBound))
    simp only [List.getElem?_eq_getElem reverseBound, Option.getD_some]
    omega
  · rw [rowEndpoint_eq hr he]
    omega

theorem nativeDomain_point_le (r : FiniteRowIndex a) {row : IBLP.Row} {p e : Nat} {sources : List Nat}
    (hr : IBLP.rowAt a r.val = some row) (hp : row.p = some p) (he : row.e = some e)
    (run : IBLP.nativeSources a r.val = some sources) (j : Nat) :
    D.point (nativeDomainIndex r sources j) ≤ D.source r.val := by
  have below := D.nativeDomainIndex_le r hr hp he run j
  have endpoint := fromRight_le_last (D.valid _ _ hr).1 (D.valid _ _ hr).2.2.1
    (Row.step_pos (D.shapes row (rowAt_mem hr))) he
  have exactEndpoint := rowEndpoint_eq hr he
  exact D.point_increasing.monotoneOn
    (by change nativeDomainIndex r sources j ≤ a.length + 1; have := r.property.2; omega)
    (by change rowEndpoint a r.val ≤ a.length + 1; have := r.property.2; omega) below

theorem nativeDomain_value (r : FiniteRowIndex a) {row : IBLP.Row} {p e : Nat} {sources : List Nat}
    (hr : IBLP.rowAt a r.val = some row) (hp : row.p = some p) (he : row.e = some e)
    (run : IBLP.nativeSources a r.val = some sources) (j : Nat) :
    D.nativePoint r sources (nativeDomainIndex r sources j) = D.point (nativeDomainIndex r sources j) := by
  have below := D.nativeDomainIndex_le r hr hp he run j
  have endpoint := fromRight_le_last (D.valid _ _ hr).1 (D.valid _ _ hr).2.2.1
    (Row.step_pos (D.shapes row (rowAt_mem hr))) he
  have exactEndpoint := rowEndpoint_eq hr he
  have value := D.nativePoint_old r sources (nativeDomainIndex r sources j)
  have shift : IBLP.shiftAfter r.val sources.length (nativeDomainIndex r sources j) = nativeDomainIndex r sources j := by
    simp only [IBLP.shiftAfter, if_neg (by omega : ¬ r.val < nativeDomainIndex r sources j)]
  rwa [shift] at value

theorem nativeDomain_image (r : FiniteRowIndex a) (sources : List Nat) (j : Nat) (bound : j ≤ sources.length) :
    D.nativeImage r (nativeDomainIndex r sources j) = D.nativePoint r sources (r.val + j + 1) := by
  by_cases before : j < sources.length
  · rw [nativeDomainIndex, if_pos before]
    have position : r.val + j + 1 = r.val + 1 + j := by omega
    rw [position, D.nativePoint_inserted r sources j before]
    rfl
  · have last : j = sources.length := by omega
    subst j
    rw [nativeDomainIndex, if_neg (Nat.lt_irrefl _), D.nativeImage_endpoint]
    have value := D.nativePoint_old r sources (r.val + 1)
    have shift : IBLP.shiftAfter r.val sources.length (r.val + 1) = r.val + sources.length + 1 := by
      simp only [IBLP.shiftAfter, if_pos (Nat.lt_succ_self r.val)]
      omega
    exact (shift ▸ value).symm

end IBLP.FiniteBoundedData
