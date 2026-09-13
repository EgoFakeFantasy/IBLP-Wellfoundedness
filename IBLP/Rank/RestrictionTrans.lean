import IBLP.Rank.WordRestriction

namespace IBLP.CutRestriction
open FullMarkedBLP
universe u v
variable {S : Type v} {C : CutSpace.{u} S}

theorem trans {F G H : CutAction C} (small : CutRestriction F G) (large : CutRestriction G H) :
    CutRestriction F H where
  bound_le := small.bound_le.trans large.bound_le
  act_eq := by
    intro z
    rw [small.act_eq, large.act_eq, C.cut_cut, min_eq_left small.bound_le]
  rho_eq := by
    intro eta
    rw [small.rho_eq, large.rho_eq, min_assoc, min_eq_right small.bound_le]

end IBLP.CutRestriction
