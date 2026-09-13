import IBLP.Extender.SetLike

namespace IBLP.Extender
open FullMarkedBLP Derivation
universe u
variable {stage : ModelStage.{u}} {alpha : Ordinal.{u}}

noncomputable def Derivation.IndexMap.toRepresentative (p : IndexMap stage alpha) : Representative stage alpha :=
  ⟨stage.hierarchy alpha, stage.rankInclude _ p.graph, p.function⟩

theorem Derivation.IndexMap.toRepresentative_value (p : IndexMap stage alpha) (x : Seed stage alpha) :
    p.toRepresentative.value x = stage.rankInclude alpha (Representative.indexValue p x) := by
  apply (p.toRepresentative.value_unique x (stage.rankInclude alpha (Representative.indexValue p x)) ?_).symm
  exact Representative.indexValue_edge p x

noncomputable def identityRepresentative (ha : Order.IsSuccLimit alpha) : Representative stage alpha :=
  (identityIndex ha).toRepresentative

theorem identityRepresentative_value (ha : Order.IsSuccLimit alpha) (x : Seed stage alpha) :
    (identityRepresentative ha).value x = stage.rankInclude _ x := by
  rw [identityRepresentative, IndexMap.toRepresentative_value, indexValue_identity]

theorem bounded_index_value (ha : Order.IsSuccLimit alpha)
    (f : BoundedRepresentative stage alpha (stage.hierarchy alpha)) (x : Seed stage alpha) :
    (IndexMap.ofFunction ha f.graph f.function).toRepresentative.value x = f.toRepresentative.value x :=
  f.toRepresentative.value_unique x _ ((IndexMap.ofFunction ha f.graph f.function).toRepresentative.value_edge x)

end IBLP.Extender
