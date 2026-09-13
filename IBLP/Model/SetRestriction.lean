import IBLP.Model.Relativization
import IBLP.Model.Ordinals

namespace IBLP
open FullMarkedBLP FirstOrder Language
universe u

namespace TransitiveClass.ElementaryMap

/-- Restrict an actual elementary map to the members of an internal set. -/
def setMap {M N : TransitiveClass.{u}} (j : M.ElementaryMap N) (domain : M.Element) :
    SetDomain domain.val → SetDomain (j domain).val := fun x =>
  ⟨(j (M.setInclude domain x)).val, (j.mem_iff _ _).mpr x.property⟩

@[simp] theorem setMap_val {M N : TransitiveClass.{u}} (j : M.ElementaryMap N)
    (domain : M.Element) (x : SetDomain domain.val) :
    (j.setMap domain x).val = (j (M.setInclude domain x)).val := rfl

/-- The restricted map is elementary for the complete membership structures,
including when the restricting set is a successor rank level. -/
def restrictToSet {M N : TransitiveClass.{u}} (j : M.ElementaryMap N) (domain : M.Element) :
    ElementaryEmbedding membershipLanguage (SetDomain domain.val) (SetDomain (j domain).val) where
  toFun := j.setMap domain
  map_formula' := by
    intro n phi values
    have h := j.realize_iff (TransitiveClass.setFormula phi)
      (Fin.snoc (M.setInclude domain ∘ values) domain)
    have tuple : j ∘ Fin.snoc (M.setInclude domain ∘ values) domain =
        Fin.snoc (N.setInclude (j domain) ∘ (j.setMap domain ∘ values)) (j domain) := by
      funext i
      cases i using Fin.lastCases with
      | last => simp
      | cast i =>
        simp only [Function.comp_apply, Fin.snoc_castSucc]
        rfl
    rw [tuple, N.setFormula_realize, M.setFormula_realize] at h
    exact h

@[simp] theorem restrictToSet_val {M N : TransitiveClass.{u}} (j : M.ElementaryMap N)
    (domain : M.Element) (x : SetDomain domain.val) :
    (j.restrictToSet domain x).val = (j (M.setInclude domain x)).val := rfl

end TransitiveClass.ElementaryMap
end IBLP
