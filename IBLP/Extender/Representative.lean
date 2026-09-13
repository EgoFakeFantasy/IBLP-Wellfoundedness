import IBLP.Extender.TupleSystem

namespace IBLP.Extender
open FullMarkedBLP
universe u

/-- A representative is an actual function graph in M. Its range is a set
in M, with no requirement that its values or graph lie in the bounded rank. -/
structure Representative (stage : ModelStage.{u}) (alpha : Ordinal.{u}) where
  range : stage.model.Element
  graph : stage.model.Element
  function : ZFSet.IsFunc (stage.hierarchy alpha).val range.val graph.val

namespace Representative
variable {stage : ModelStage.{u}} {alpha : Ordinal.{u}}

noncomputable def value (f : Representative stage alpha) (x : Derivation.Seed stage alpha) : stage.model.Element :=
  let y := zfGraphFunction f.function ⟨x.val, (stage.mem_hierarchy alpha x.val).mpr x.property⟩
  stage.model.member f.range y.val y.property

theorem value_edge (f : Representative stage alpha) (x : Derivation.Seed stage alpha) :
    ZFSet.pair x.val (f.value x).val ∈ f.graph.val := zfGraphFunction_edge f.function _

theorem value_mem (f : Representative stage alpha) (x : Derivation.Seed stage alpha) :
    (f.value x).val ∈ f.range.val :=
  (ZFSet.pair_mem_prod.mp (f.function.1 (f.value_edge x))).2

theorem value_unique (f : Representative stage alpha) (x : Derivation.Seed stage alpha)
    (y : stage.model.Element) (edge : ZFSet.pair x.val y.val ∈ f.graph.val) : y = f.value x :=
  Subtype.ext ((f.function.2 x.val ((stage.mem_hierarchy alpha x.val).mpr x.property)).unique edge (f.value_edge x))

theorem edge_iff_value (f : Representative stage alpha) (x : Derivation.Seed stage alpha) (y : stage.model.Element) :
    ZFSet.pair x.val y.val ∈ f.graph.val ↔ y = f.value x :=
  ⟨f.value_unique x y, fun h => h ▸ f.value_edge x⟩

noncomputable def pullback (f : Representative stage alpha) (p : Derivation.IndexMap stage alpha) :
    Representative stage alpha where
  range := f.range
  graph := stage.compGraph (stage.rankInclude _ p.graph) f.graph
    (stage.hierarchy alpha) (stage.hierarchy alpha) (stage.hierarchy alpha) f.range
    p.function f.function (fun _ h => h)
  function := stage.compGraph_function _ _ _ _ _ _ p.function f.function (fun _ h => h)

noncomputable def indexValue (p : Derivation.IndexMap stage alpha) (x : Derivation.Seed stage alpha) :
    Derivation.Seed stage alpha :=
  let y := zfGraphFunction p.function ⟨x.val, (stage.mem_hierarchy alpha x.val).mpr x.property⟩
  ⟨y.val, (stage.mem_hierarchy alpha y.val).mp y.property⟩

theorem indexValue_edge (p : Derivation.IndexMap stage alpha) (x : Derivation.Seed stage alpha) :
    ZFSet.pair x.val (indexValue p x).val ∈ p.graph.val := zfGraphFunction_edge p.function _

theorem pullback_value (f : Representative stage alpha) (p : Derivation.IndexMap stage alpha)
    (x : Derivation.Seed stage alpha) : (f.pullback p).value x = f.value (indexValue p x) := by
  apply (Representative.value_unique _ _ _ ?_).symm
  exact (stage.compGraph_edge_iff _ _ _ _ _ _ p.function f.function (fun _ h => h) _ _).mpr
    ⟨(indexValue p x).val, indexValue_edge p x, f.value_edge (indexValue p x)⟩

end Representative
end IBLP.Extender
