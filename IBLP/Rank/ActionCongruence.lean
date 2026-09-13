import IBLP.Rank.WordAction

namespace IBLP.CutAction
universe u v
variable {S : Type v} {C : CutSpace.{u} S}

theorem ext {F G : CutAction C} (act : F.act = G.act) (rho : F.rho = G.rho) (bound : F.bound = G.bound) : F = G := by
  cases F
  cases G
  cases act
  cases rho
  cases bound
  rfl

theorem comp_assoc (F G H : CutAction C) : (F.comp G).comp H = F.comp (G.comp H) := rfl

end IBLP.CutAction
