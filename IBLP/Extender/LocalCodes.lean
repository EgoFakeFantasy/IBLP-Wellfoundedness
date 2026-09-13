import IBLP.Extender.SetLike
import IBLP.Model.FunctionBooks
import IBLP.Model.SetCollapse

namespace IBLP.Extender
open FullMarkedBLP Derivation
universe u
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}

theorem BoundedRepresentative.ext_graph {bound : stage.model.Element}
    {f g : BoundedRepresentative stage alpha bound} (same : f.graph = g.graph) : f = g := by
  cases f
  cases g
  cases same
  rfl

namespace LocalCodes

noncomputable def domain (stage : ModelStage.{u}) (alpha beta : Ordinal.{u}) (bound : stage.model.Element) :
    stage.model.Element := stage.product (stage.hierarchy beta) (stage.functionBook (stage.hierarchy alpha) bound)

variable (bound : stage.model.Element)

noncomputable def encode (c : Seed stage beta × BoundedRepresentative stage alpha bound) :
    SetDomain (domain stage alpha beta bound).val :=
  ⟨ZFSet.pair c.1.val c.2.graph.val, by
    rw [domain, stage.product_val, ZFSet.pair_mem_prod]
    exact ⟨(stage.mem_hierarchy beta c.1.val).mpr c.1.property,
      (stage.mem_functionBook _ _ c.2.graph).mpr c.2.function⟩⟩

theorem encode_injective : Function.Injective (encode (alpha := alpha) (beta := beta) bound) := by
  intro a b h
  have same : ZFSet.pair a.1.val a.2.graph.val = ZFSet.pair b.1.val b.2.graph.val :=
    congrArg Subtype.val h
  obtain ⟨seeds, graphs⟩ := ZFSet.pair_inj.mp same
  exact Prod.ext (Subtype.ext seeds) (BoundedRepresentative.ext_graph (Subtype.ext graphs))

theorem encode_surjective : Function.Surjective (encode (alpha := alpha) (beta := beta) bound) := by
  intro c
  have hc := c.property
  change c.val ∈ (stage.product (stage.hierarchy beta) (stage.functionBook (stage.hierarchy alpha) bound)).val at hc
  rw [stage.product_val] at hc
  obtain ⟨a, ha, graph, hg, pair⟩ := ZFSet.mem_prod.mp hc
  let seed : Seed stage beta := ⟨a, (stage.mem_hierarchy beta a).mp ha⟩
  let g := stage.model.member (stage.functionBook (stage.hierarchy alpha) bound) graph hg
  let f : BoundedRepresentative stage alpha bound := ⟨g, (stage.mem_functionBook _ _ g).mp hg⟩
  exact ⟨⟨seed, f⟩, Subtype.ext pair.symm⟩

noncomputable def equiv :
    (Seed stage beta × BoundedRepresentative stage alpha bound) ≃ SetDomain (domain stage alpha beta bound).val :=
  Equiv.ofBijective (encode bound) ⟨encode_injective bound, encode_surjective bound⟩

noncomputable def representative (c : SetDomain (domain stage alpha beta bound).val) :
    SeededRepresentative stage alpha beta :=
  ⟨((equiv bound).symm c).1, ((equiv bound).symm c).2.toRepresentative⟩

theorem representative_encode (c : Seed stage beta × BoundedRepresentative stage alpha bound) :
    representative bound (encode bound c) = ⟨c.1, c.2.toRepresentative⟩ := by
  unfold representative
  rw [show encode bound c = equiv bound c from rfl, Equiv.symm_apply_apply]

theorem code_val (c : SetDomain (domain stage alpha beta bound).val) :
    c.val = ZFSet.pair (representative bound c).seed.val (representative bound c).representative.graph.val := by
  have h := congrArg Subtype.val ((equiv bound).apply_symm_apply c)
  exact h.symm

end LocalCodes
end IBLP.Extender
