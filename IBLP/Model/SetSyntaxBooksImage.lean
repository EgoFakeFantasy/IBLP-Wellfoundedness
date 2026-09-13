import IBLP.Model.SetSyntaxBooks
import IBLP.Model.CountableImage

namespace IBLP
open FullMarkedBLP
universe u

namespace ModelStage
variable (source target : ModelStage.{u}) (j : source.model.ElementaryMap target.model)

theorem setTuple_image {n : Nat} (values : Fin n → source.model.Element) :
    j (source.setTuple values) = target.setTuple (j ∘ values) := by
  induction n with
  | zero => exact source.ordinal_zero_image target j
  | succ n ih =>
    rw [setTuple, source.orderedPair_image target j, ih]
    rfl

theorem naturalTuple_image {n : Nat} (values : Fin n → Nat) :
    j (source.setTuple (fun i => source.ordinal (values i : Ordinal.{u}))) =
      target.setTuple (fun i => target.ordinal (values i : Ordinal.{u})) := by
  rw [source.setTuple_image target j]
  congr 1
  funext i
  exact source.ordinal_nat_image target j (values i)

/-- Every relation on finite natural tuples is fixed, including arbitrary
countable syntax tables. The proof transports its actual countable set of
tuple values and proves that every tuple itself is fixed. -/
theorem natRelation_image {n : Nat} (relation : (Fin n → Nat) → Prop) :
    j (source.natRelation relation) = target.natRelation relation := by
  classical
  let T := {v : Fin n → Nat // relation v}
  by_cases nonempty : Nonempty T
  · letI : Encodable T := Encodable.ofCountable T
    let default : T := Classical.choice nonempty
    let enumeration (k : Nat) : T := (Encodable.decode (α := T) k).getD default
    have enumeration_encode (t : T) : enumeration (Encodable.encode t) = t := by
      simp only [enumeration, Encodable.encodek, Option.getD_some]
    have representation (stage : ModelStage.{u}) :
        stage.natRelation relation = stage.countableRange
          (fun k => stage.setTuple (fun i => stage.ordinal ((enumeration k).val i : Ordinal.{u}))) := by
      apply Subtype.ext
      apply ZFSet.ext
      intro z
      rw [stage.natRelation_val, zfNatRelation, stage.countableRange_val, ZFSet.mem_range, ZFSet.mem_range]
      constructor
      · rintro ⟨t, value⟩
        refine ⟨Encodable.encode t, ?_⟩
        rw [enumeration_encode, stage.setTuple_val]
        exact (setTuple_nat t.val).trans value
      · rintro ⟨k, value⟩
        refine ⟨enumeration k, ?_⟩
        rw [stage.setTuple_val] at value
        exact (setTuple_nat (enumeration k).val).symm.trans value
    rw [representation source, source.countableRange_image target j, representation target]
    congr 1
    funext k
    exact source.naturalTuple_image target j (enumeration k).val
  · have empty : zfNatRelation.{u} relation = ∅ := by
      apply (ZFSet.eq_empty _).mpr
      intro z hz
      obtain ⟨t, _⟩ := ZFSet.mem_range.mp hz
      exact nonempty ⟨t⟩
    have zero (stage : ModelStage.{u}) : stage.natRelation relation = stage.ordinal 0 := by
      apply Subtype.ext
      simpa only [stage.natRelation_val, ordinal, Ordinal.toZFSet_zero] using empty
    rw [zero source, source.ordinal_zero_image target j, zero target]

/-- All six fixed syntax-book parameters are preserved by every actual
elementary map between the maintained model stages. No extra fixed-table
assumption is added to satisfaction or to the future Good formula. -/
theorem syntaxBooks_image (i : Fin 6) :
    j (source.syntaxBooks i) = target.syntaxBooks i := by
  fin_cases i <;> exact source.natRelation_image target j _

theorem syntaxBooks_comp_image : j ∘ source.syntaxBooks = target.syntaxBooks := by
  funext i
  exact source.syntaxBooks_image target j i

end ModelStage
end IBLP
