import IBLP.ParallelTrace

namespace IBLP

theorem FactorTrace.internal_predecessor {a : Pattern} {target start parent child : Nat} {rows : List Nat}
    (trace : FactorTrace a target start rows) (pair : (parent, child) ∈ rows.zip rows.tail) :
    predecessor a parent = some child := by
  induction trace with
  | single => simp at pair
  | @cons start next rows pred less inner ih =>
    obtain ⟨rest, same⟩ := List.head?_eq_some_iff.mp inner.head
    simp only [same, List.tail_cons, List.zip_cons_cons] at pair
    rcases List.mem_cons.mp pair with equal | innerPair
    · cases equal
      exact pred
    · exact ih (by simpa only [same, List.tail_cons] using innerPair)

end IBLP
