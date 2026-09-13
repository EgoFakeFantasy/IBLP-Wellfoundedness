import Mathlib.SetTheory.ZFC.Basic
import Mathlib.SetTheory.Cardinal.Basic

namespace IBLP
namespace Extender

universe u v

variable {A : Type v} (r : A → A → Prop)

/-- 集合式前驱保证每个坍缩值是 ZFSet，而不要求整个类规模对象域是一个集合。 -/
noncomputable def collapse [∀ a, Small.{u} {b // r b a}] (wf : WellFounded r) : A → ZFSet.{u} :=
  wf.fix (fun a rec => ZFSet.range (fun b : {b // r b a} => rec b.val b.property))

theorem collapse_eq [∀ a, Small.{u} {b // r b a}] (wf : WellFounded r) (a : A) :
    collapse r wf a = ZFSet.range (fun b : {b // r b a} => collapse r wf b.val) := by
  unfold collapse
  rw [WellFounded.fix_eq]

theorem mem_collapse_iff [∀ a, Small.{u} {b // r b a}] (wf : WellFounded r) (a : A) (z : ZFSet.{u}) :
    z ∈ collapse r wf a ↔ ∃ b, r b a ∧ collapse r wf b = z := by
  rw [collapse_eq, ZFSet.mem_range]
  exact ⟨fun ⟨⟨b, hb⟩, he⟩ => ⟨b, hb, he⟩, fun ⟨b, hb, he⟩ => ⟨⟨b, hb⟩, he⟩⟩

theorem collapse_injective [∀ a, Small.{u} {b // r b a}] (wf : WellFounded r)
    (extensional : ∀ a b, (∀ z, r z a ↔ r z b) → a = b) :
    Function.Injective (collapse r wf : A → ZFSet.{u}) := by
  intro a
  induction a using wf.induction with
  | h a ih =>
    intro b he
    apply extensional a b
    intro z
    constructor
    · intro hz
      have hm : collapse r wf z ∈ collapse r wf b := by
        rw [← he]
        exact (mem_collapse_iff r wf _ _).mpr ⟨z, hz, rfl⟩
      obtain ⟨y, hy, same⟩ := (mem_collapse_iff r wf _ _).mp hm
      have hzy := ih z hz same.symm
      simpa only [hzy] using hy
    · intro hz
      have hm : collapse r wf z ∈ collapse r wf a := by
        rw [he]
        exact (mem_collapse_iff r wf _ _).mpr ⟨z, hz, rfl⟩
      obtain ⟨y, hy, same⟩ := (mem_collapse_iff r wf _ _).mp hm
      have hyz := ih y hy same
      simpa only [hyz] using hy

theorem collapse_mem_iff [∀ a, Small.{u} {b // r b a}] (wf : WellFounded r)
    (extensional : ∀ a b, (∀ z, r z a ↔ r z b) → a = b) (a b : A) :
    collapse r wf a ∈ collapse r wf b ↔ r a b := by
  rw [mem_collapse_iff]
  constructor
  · rintro ⟨c, hc, he⟩
    have hca := collapse_injective r wf extensional he
    simpa only [hca] using hc
  · intro h
    exact ⟨a, h, rfl⟩

theorem collapse_range_transitive [∀ a, Small.{u} {b // r b a}] (wf : WellFounded r)
    {x y : ZFSet.{u}} (hy : y ∈ Set.range (collapse r wf)) (hx : x ∈ y) :
    x ∈ Set.range (collapse r wf) := by
  obtain ⟨a, rfl⟩ := hy
  obtain ⟨b, _, hb⟩ := (mem_collapse_iff r wf a x).mp hx
  exact ⟨b, hb⟩

/-- 坍缩由递归方程唯一确定，供内部与外部计算结果的一致性使用。 -/
theorem collapse_unique [∀ a, Small.{u} {b // r b a}] (wf : WellFounded r)
    (f : A → ZFSet.{u}) (hf : ∀ a z, z ∈ f a ↔ ∃ b, r b a ∧ f b = z) :
    f = collapse r wf := by
  funext a
  induction a using wf.induction with
  | h a ih =>
    apply ZFSet.ext
    intro z
    rw [hf, mem_collapse_iff]
    constructor
    · rintro ⟨b, hb, he⟩
      exact ⟨b, hb, (ih b hb).symm.trans he⟩
    · rintro ⟨b, hb, he⟩
      exact ⟨b, hb, (ih b hb).trans he⟩

end Extender
end IBLP
