import IBLP.Rank.WordAction

namespace IBLP.CutAction
universe u v w
variable {S : Type v} {T : Type w} {C : CutSpace.{u} S} {C' : CutSpace.{u} T}

/-- The three equalities needed to copy a word. Concrete graph images
provide these fields in Model.WeakActionImage. -/
structure Image (j : S → T) (ord : Ordinal.{u} → Ordinal.{u})
    (F : CutAction C) (G : CutAction C') : Prop where
  act : ∀ z, G.act (j z) = j (F.act z)
  rho : ∀ eta, G.rho (ord eta) = ord (F.rho eta)
  bound : G.bound = ord F.bound

namespace Image
variable {j : S → T} {ord : Ordinal.{u} → Ordinal.{u}}
  {F H : CutAction C} {G K : CutAction C'}

theorem comp (outer : Image j ord F G) (inner : Image j ord H K) :
    Image j ord (F.comp H) (G.comp K) where
  act := by intro z; change G.act (K.act (j z)) = _; rw [inner.act, outer.act]; rfl
  rho := by intro eta; change G.rho (K.rho (ord eta)) = _; rw [inner.rho, outer.rho]; rfl
  bound := by change G.rho K.bound = _; rw [inner.bound, outer.rho]; rfl

theorem word {fs : List (CutAction C)} {gs : List (CutAction C')}
    (head : Image j ord F G) (tail : List.Forall₂ (Image j ord) fs gs) :
    Image j ord (CutAction.word F fs) (CutAction.word G gs) := by
  induction tail generalizing F G with
  | nil => exact head
  | cons first rest ih => exact head.comp (ih first)

end Image
end IBLP.CutAction
