import IBLP.Extender.SetLike
import IBLP.Extender.WellFounded

namespace IBLP.Extender.Ultrapower
open FullMarkedBLP FirstOrder Language Derivation
universe u
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}
  (D : Derivation stage alpha beta) (ha : Order.IsSuccLimit alpha) (hb : Order.IsSuccLimit beta)
  (inaccessible : stage.model.InternalInaccessible (stage.ordinal beta))

/-- The actual transitive collapse, now with all input conditions proved. -/
noncomputable def collapsedValue : Ultrapower D ha hb → ZFSet.{u} :=
  Extender.collapse (Mem D ha hb) (wellFounded D ha hb inaccessible)

theorem collapsedValue_injective : Function.Injective (collapsedValue D ha hb inaccessible) :=
  Extender.collapse_injective (Mem D ha hb) (wellFounded D ha hb inaccessible) (extensional D ha hb)

theorem collapsedValue_mem_iff (p q : Ultrapower D ha hb) :
    collapsedValue D ha hb inaccessible p ∈ collapsedValue D ha hb inaccessible q ↔ Mem D ha hb p q :=
  Extender.collapse_mem_iff (Mem D ha hb) (wellFounded D ha hb inaccessible) (extensional D ha hb) p q

noncomputable def target : TransitiveClass.{u} :=
  collapseClass (Mem D ha hb) (wellFounded D ha hb inaccessible)

noncomputable def collapseMap (q : Ultrapower D ha hb) : (target D ha hb inaccessible).Element :=
  ⟨collapsedValue D ha hb inaccessible q, ⟨q, rfl⟩⟩

theorem collapseMap_bijective : Function.Bijective (collapseMap D ha hb inaccessible) := by
  constructor
  · intro p q h
    exact collapsedValue_injective D ha hb inaccessible (congrArg Subtype.val h)
  · intro y
    obtain ⟨q, hq⟩ := y.property
    exact ⟨q, Subtype.ext hq⟩

noncomputable def collapseEquiv :
    Language.Equiv membershipLanguage (Ultrapower D ha hb) (target D ha hb inaccessible).Element where
  toEquiv := Equiv.ofBijective (collapseMap D ha hb inaccessible) (collapseMap_bijective D ha hb inaccessible)
  map_fun' := fun f => Empty.elim f
  map_rel' := by
    intro n relation values
    obtain ⟨same⟩ := relation
    subst n
    exact collapsedValue_mem_iff D ha hb inaccessible (values 0) (values 1)

/-- The elementary embedding into the constructed transitive target.
Target closure and inclusion in M are subsequent properties, not inputs. -/
noncomputable def embedding : stage.model.ElementaryMap (target D ha hb inaccessible) :=
  (collapseEquiv D ha hb inaccessible).toElementaryEmbedding.comp (constantEmbedding D ha hb)

theorem embedding_val (x : stage.model.Element) :
    (embedding D ha hb inaccessible x).val =
      collapsedValue D ha hb inaccessible (constantEmbedding D ha hb x) := rfl

end IBLP.Extender.Ultrapower
