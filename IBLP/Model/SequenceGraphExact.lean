import IBLP.Model.ElementaryNaturals

namespace IBLP
open FullMarkedBLP
universe u

def functionDomainMatrix : RankPredicateFormula 0 2 :=
  (rankPredicateAtom rankFunctionFormula ![0, 1, 2]).ex

theorem functionDomainMatrix_realize (M : TransitiveClass.{u}) (graph domain : M.Element) :
    M.realize functionDomainMatrix ![graph, domain] ↔
      ∃ range : M.Element, ZFSet.IsFunc domain.val range.val graph.val := by
  rw [functionDomainMatrix, M.realize_ex]
  apply exists_congr
  intro range
  rw [M.realize_atom]
  have args : Fin.snoc ![graph, domain] range ∘ ![0, 1, 2] = ![graph, domain, range] := by
    funext i; fin_cases i <;> rfl
  rw [args, M.functionFormula_realize, M.function_absolute]

theorem TransitiveClass.sequenceGraph_eq_of_function (M : TransitiveClass.{u}) (f : Nat → M.Element)
    {graph range : ZFSet.{u}} (hf : ZFSet.IsFunc Ordinal.omega0.toZFSet range graph)
    (edges : ∀ n : Nat, ZFSet.pair (n : Ordinal.{u}).toZFSet (f n).val ∈ graph) :
    graph = M.sequenceGraph f := by
  apply ZFSet.ext
  intro p
  constructor
  · intro hp
    obtain ⟨i, hi, y, _, rfl⟩ := ZFSet.mem_prod.mp (hf.1 hp)
    obtain ⟨n, hn⟩ := natZFSetOmegaEquiv.surjective ⟨i, hi⟩
    have indexEq := congrArg Subtype.val hn
    change (n : Ordinal.{u}).toZFSet = i at indexEq
    have edge := edges n
    rw [indexEq] at edge
    have valueEq := (hf.2 i hi).unique edge hp
    apply ZFSet.mem_range.mpr
    exact ⟨n, by rw [indexEq, valueEq]⟩
  · intro hp
    obtain ⟨n, rfl⟩ := ZFSet.mem_range.mp hp
    exact edges n

end IBLP
