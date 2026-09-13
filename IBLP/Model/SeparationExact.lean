import IBLP.Model.Separation

namespace IBLP
open FullMarkedBLP
universe u

theorem ModelStage.separationMatrix_iff (stage : ModelStage.{u}) {n : Nat}
    (phi : RankPredicateFormula 0 (n + 1)) (values : Fin n → stage.model.Element)
    (domain result : stage.model.Element) :
    stage.model.realize (separationMatrix phi) (Fin.snoc (Fin.snoc values domain) result) ↔
      result = stage.separation phi values domain := by
  rw [separationMatrix_realize]
  constructor
  · intro h
    apply stage.model.element_ext
    intro x
    rw [stage.mem_separation]
    exact h x
  · intro h x
    rw [h, stage.mem_separation]

end IBLP
