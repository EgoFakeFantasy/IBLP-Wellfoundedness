import IBLP.TracePieces
import IBLP.Rank.ActionCongruence

namespace IBLP
universe u v

theorem FactorPrefix.toFactorTrace {a : Pattern} {target start : Nat} {rows : List Nat}
    (h : FactorPrefix a target start rows) (nonempty : rows ≠ []) : FactorTrace a target start rows := by
  induction h with
  | nil => exact False.elim (nonempty rfl)
  | @cons r next rows hp hn inner ih =>
    by_cases empty : rows = []
    · cases empty
      cases inner
      exact .single hp hn
    · exact .cons hp hn (ih empty)

theorem FactorTrace.word_append {a : Pattern} {S : Type v} {C : CutSpace.{u} S} {O : OrdinalView C}
    {theta : Nat → Ordinal.{u}} (D : TraceActions a C O theta)
    {boundary start target : Nat} {front suffix : List Nat}
    (h : FactorTrace a boundary start front) (after : FactorTrace a target boundary suffix) :
    (h.append after).word D = (h.word D).comp (after.word D) := by
  induction h with
  | single hp hn => exact FactorTrace.word_cons D hp hn after
  | cons hp hn inner ih =>
    change (FactorTrace.cons hp hn (inner.append after)).word D = _
    rw [FactorTrace.word_cons D hp hn (inner.append after), FactorTrace.word_cons D hp hn inner,
      ih, CutAction.comp_assoc]

end IBLP
