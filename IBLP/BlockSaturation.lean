import IBLP.PrefixGeometry

namespace IBLP

/-- The manuscript's conditional entry saturation: only carriers below
the block endpoint whose predecessor remains above the block start.
No condition is asserted at a factor whose predecessor has left the block. -/
def BlockSaturated (a : Pattern) (lower upper : Nat) : Prop :=
  ∀ r row p e q, r < upper → lower ≤ p → rowAt a r = some row →
    row.p = some p → row.e = some e → penultimate a e = some q → q ≤ p

theorem Saturated.block {a : Pattern} (saturated : Saturated a) (lower upper : Nat) :
    BlockSaturated a lower upper :=
  fun r row p e q _ _ hr hp he hq => saturated r row p e q hr hp he hq

theorem BlockSaturated.congr_prefix {a b : Pattern} {lower upper : Nat}
    (saturated : BlockSaturated a lower upper) (valid : BasicValid a) (shapes : OrdinaryShape a)
    (same : ∀ i, i < upper → rowAt b i = rowAt a i) : BlockSaturated b lower upper := by
  intro r row p e q before tail atRow hp he hq
  have originalAt := (same r before).symm.trans atRow
  have endpointBound := fromRight_le_last (valid _ _ originalAt).1 (valid _ _ originalAt).2.2.1
    (Row.step_pos (shapes row (rowAt_mem originalAt))) he
  have oldQ : penultimate a e = some q := by
    simpa only [penultimate, same e (endpointBound.trans_lt before)] using hq
  exact saturated r row p e q before tail originalAt hp he oldQ

end IBLP
