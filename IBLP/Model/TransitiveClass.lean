import IBLP.Rank.CutSpace
import IBLP.Extender.Collapse

namespace IBLP
open FullMarkedBLP

universe u

/-- 环境集合宇宙中的传递类。这里不暗含 ZFC、序数齐全或可数封闭。 -/
structure TransitiveClass where
  carrier : Set ZFSet.{u}
  transitive : ∀ {x y}, x ∈ y → y ∈ carrier → x ∈ carrier

namespace TransitiveClass

def Element (M : TransitiveClass.{u}) := {x : ZFSet.{u} // x ∈ M.carrier}

instance membershipStructure (M : TransitiveClass.{u}) : membershipLanguage.Structure M.Element where
  funMap := fun f => Empty.elim f
  RelMap := fun {n} r xs => by
    obtain ⟨hn⟩ := r
    subst n
    exact (xs 0).val ∈ (xs 1).val

def member (M : TransitiveClass.{u}) (x : M.Element) (z : ZFSet.{u}) (hz : z ∈ x.val) : M.Element :=
  ⟨z, M.transitive hz x.property⟩

theorem element_ext (M : TransitiveClass.{u}) {x y : M.Element}
    (h : ∀ z : M.Element, z.val ∈ x.val ↔ z.val ∈ y.val) : x = y := by
  apply Subtype.ext
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    exact (h (M.member x z hz)).mp hz
  · intro hz
    exact (h (M.member y z hz)).mpr hz

/-- 模型域与环境秩截段的交是传递类；与构造的内部累计层的一致性见 Model.Hierarchy。 -/
def rankPart (M : TransitiveClass.{u}) (alpha : Ordinal.{u}) : TransitiveClass.{u} where
  carrier := {x | x ∈ M.carrier ∧ x.rank < alpha}
  transitive := fun hxy hy => ⟨M.transitive hxy hy.1, (ZFSet.rank_lt_of_mem hxy).trans hy.2⟩

/-- 模型内的秩截段元素；保留模型成员资格，不取环境的整个 V_alpha。 -/
abbrev RankElement (M : TransitiveClass.{u}) (alpha : Ordinal.{u}) := (M.rankPart alpha).Element

/-- 模型中的初等性逐公式定义，不引入宇宙真谓词常量。 -/
abbrev ElementaryMap (M N : TransitiveClass.{u}) :=
  FirstOrder.Language.ElementaryEmbedding membershipLanguage M.Element N.Element

noncomputable def sequenceGraph (M : TransitiveClass.{u}) (f : Nat → M.Element) : ZFSet.{u} :=
  ZFSet.range (fun n : Nat => ZFSet.pair (n : Ordinal.{u}).toZFSet (f n).val)

/-- 对环境中任意可数元素序列，其完整函数图仍在 M 中。 -/
def CountablyClosed (M : TransitiveClass.{u}) : Prop :=
  ∀ f : Nat → M.Element, M.sequenceGraph f ∈ M.carrier

def OrdinalComplete (M : TransitiveClass.{u}) : Prop := ∀ a : Ordinal.{u}, a.toZFSet ∈ M.carrier

end TransitiveClass

/-- 截断封闭的接口；ModelStage.rankClosed 从实际内部累计层构造其实例。 -/
structure RankClosedClass extends TransitiveClass.{u} where
  cut_mem : ∀ {z}, z ∈ carrier → ∀ alpha : Ordinal.{u}, z ∩ ZFSet.vonNeumann alpha ∈ carrier

noncomputable def RankClosedClass.cutSpace (M : RankClosedClass.{u}) :
    CutSpace.{u} M.toTransitiveClass.Element where
  rank := fun x => x.val.rank
  mem := fun x y => x.val ∈ y.val
  cut := fun alpha z => ⟨(truncate alpha z.val).val, M.cut_mem z.property alpha⟩
  mem_cut := fun _ _ _ => by simp only [truncate, ZFSet.mem_inter, ZFSet.mem_vonNeumann]
  rank_mem_lt := fun h => ZFSet.rank_lt_of_mem h
  cut_rank_le := fun _ _ => truncate_rank_le _ _
  ext := M.toTransitiveClass.element_ext

def universeClass : RankClosedClass.{u} where
  carrier := Set.univ
  transitive := fun _ _ => Set.mem_univ _
  cut_mem := fun _ _ => Set.mem_univ _

theorem universeClass_countablyClosed : universeClass.toTransitiveClass.CountablyClosed :=
  fun _ => Set.mem_univ _

theorem universeClass_ordinalComplete : universeClass.toTransitiveClass.OrdinalComplete :=
  fun _ => Set.mem_univ _

noncomputable def collapseClass {A : Type v} (r : A → A → Prop)
    [∀ a, Small.{u} {b // r b a}] (wf : WellFounded r) : TransitiveClass.{u} where
  carrier := Set.range (Extender.collapse r wf)
  transitive := fun hx hy => Extender.collapse_range_transitive r wf hy hx

end IBLP
