import IBLP.Rank.I3
import IBLP.Syntax

namespace IBLP
open FullMarkedBLP

universe u

/-- 根的六个 owner；只用于构造根证书，不要求后续图案共享全域 owner。 -/
noncomputable def rootOwner {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j : RankElementaryEmbedding lambda) : Nat → RankElementaryEmbedding lambda
  | 1 => j
  | 2 => j
  | 3 => j.comp j
  | 4 => shiftEmbedding hl j 2
  | 5 => (shiftEmbedding hl j 2).comp (shiftEmbedding hl j 2)
  | 6 => shiftEmbedding hl j 4
  | _ => j

/-- 显式 L 步边连同隐含末边。 -/
def Row.edgePairs (row : IBLP.Row) (r : Nat) : List (Nat × Nat) :=
  let full := row.columns ++ [r + 1]
  full.zip (full.drop row.step)

def Row.RealizesEdges {lambda : Ordinal.{u}} (row : IBLP.Row) (r : Nat)
    (theta : Nat → OrdinalDomain lambda) (owner : RankElementaryEmbedding lambda) : Prop :=
  ∀ edge ∈ row.edgePairs r, rankOrdinalAction owner (theta edge.1) = theta edge.2

theorem rootOwner_criticalPoint {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {j : RankElementaryEmbedding lambda}
    {c : OrdinalDomain lambda} (hc : RankCriticalPoint j c)
    {r minimum : Nat} {row : IBLP.Row} (hr : IBLP.rowAt IBLP.root r = some row)
    (hm : row.columns.head? = some minimum) :
    RankCriticalPoint (rootOwner hl j r) (rankCriticalSequence j c minimum) := by
  have hp := IBLP.rowAt_pos hr
  have hle : r ≤ 6 := IBLP.rowAt_le_length hr
  have h2 := shiftEmbedding_criticalPoint hl hc 2
  have h4 := shiftEmbedding_criticalPoint hl hc 4
  have hjj : RankCriticalPoint (j.comp j) c := by
    simpa only [min_self] using rankCriticalPoint_comp hc hc
  have h22 : RankCriticalPoint ((shiftEmbedding hl j 2).comp (shiftEmbedding hl j 2))
      (rankCriticalSequence j c 2) := by
    simpa only [min_self] using rankCriticalPoint_comp h2 h2
  interval_cases r <;> norm_num [IBLP.rowAt, IBLP.root] at hr <;> subst row <;>
    simp only [List.head?_cons, Option.some.injEq] at hm <;> subst minimum <;>
    simp only [rootOwner, rankCriticalSequence] <;> first | exact hc | exact hjj | exact h2 | exact h22 | exact h4

theorem rootOwner_edges {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j : RankElementaryEmbedding lambda) (c : OrdinalDomain lambda)
    {r : Nat} {row : IBLP.Row} (hr : IBLP.rowAt IBLP.root r = some row) :
    row.RealizesEdges r (rankCriticalSequence j c) (rootOwner hl j r) := by
  have hp := IBLP.rowAt_pos hr
  have hle : r ≤ 6 := IBLP.rowAt_le_length hr
  have h20 := shiftEmbedding_on_tail hl j c 2 0
  have h21 := shiftEmbedding_on_tail hl j c 2 1
  have h22 := shiftEmbedding_on_tail hl j c 2 2
  have h23 := shiftEmbedding_on_tail hl j c 2 3
  have h40 := shiftEmbedding_on_tail hl j c 4 0
  have h41 := shiftEmbedding_on_tail hl j c 4 1
  have h42 := shiftEmbedding_on_tail hl j c 4 2
  have hj (i : Nat) : rankOrdinalAction j (rankCriticalSequence j c i) =
      rankCriticalSequence j c (i + 1) := rfl
  interval_cases r <;> norm_num [IBLP.rowAt, IBLP.root] at hr <;> subst row <;>
    simp [Row.RealizesEdges, Row.edgePairs, rootOwner, rankOrdinalAction_comp,
      hj, h20, h21, h22, h23, h40, h41, h42]

/-- 已实现六行的初始有限边表和临界点，不包含尚未证明的有界图闭包。 -/
theorem exists_root_owners_of_i3 (h : I3.{u}) :
    ∃ (lambda : Ordinal.{u}) (_ : Order.IsSuccLimit lambda)
      (theta : Nat → OrdinalDomain lambda) (owner : Nat → RankElementaryEmbedding lambda),
      StrictMono theta ∧
      (∀ i, ∃ k : Cardinal.{u}, k.ord = (theta i).val) ∧
      (∀ i, Cardinal.IsInaccessible (theta i).val.card) ∧
      (∀ r row, IBLP.rowAt IBLP.root r = some row → row.RealizesEdges r theta (owner r)) ∧
      (∀ r row minimum, IBLP.rowAt IBLP.root r = some row → row.columns.head? = some minimum →
        RankCriticalPoint (owner r) (theta minimum)) := by
  obtain ⟨lambda, hl, j, c, hc⟩ := i3_iff_criticalPoint.mp h
  refine ⟨lambda, hl, rankCriticalSequence j c, rootOwner hl j,
    rankCriticalSequence_strictMono hc, rankCriticalSequence_cardinal hl hc,
    rankCriticalSequence_isInaccessible hl hc, ?_, ?_⟩
  · exact fun _ _ hr => rootOwner_edges hl j c hr
  · exact fun _ _ _ hr hm => rootOwner_criticalPoint hl hc hr hm

end IBLP
