import IBLP.Model.BoundedGraph

namespace IBLP.TransitiveClass
open FullMarkedBLP
universe u

/-- A complete set graph has the same elementary meaning in any two
transitive ambient classes that contain its exact domain and range. -/
theorem graphElementary_absolute (M N : IBLP.TransitiveClass.{u})
    (graph domain range : M.Element) (graph' domain' range' : N.Element)
    (hg : graph.val = graph'.val) (hd : domain.val = domain'.val) (hr : range.val = range'.val) :
    M.GraphElementary graph domain range ↔ N.GraphElementary graph' domain' range' := by
  rcases graph with ⟨g, hgm⟩
  rcases domain with ⟨d, hdm⟩
  rcases range with ⟨r, hrm⟩
  rcases graph' with ⟨g', hgn⟩
  rcases domain' with ⟨d', hdn⟩
  rcases range' with ⟨r', hrn⟩
  change g = g' at hg
  change d = d' at hd
  change r = r' at hr
  subst g'
  subst d'
  subst r'
  simp only [GraphElementary, M.function_absolute, N.function_absolute,
    M.graphApplies_absolute, N.graphApplies_absolute, M.setFormula_realize, N.setFormula_realize]
  rfl

end IBLP.TransitiveClass
