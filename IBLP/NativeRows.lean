import IBLP.NativeEndpoints

/-! Literal prefix/family/suffix lookup calculations follow the fixed
upstream native list proofs (Apache-2.0), for the original IBLP program. -/
namespace IBLP

theorem native_decomposition {a b : Pattern} {r : Nat} {sources : List Nat}
    (run : native a r = some (b, sources)) : ∃ row block,
    rowAt a r = some row ∧ nativeSources a r = some sources ∧ nativeBlock row r sources = some block ∧
    b = a.take (r - 1) ++ block ++ (a.drop r).map (Row.shiftAfter r sources.length) := by
  obtain ⟨row, hr, rest⟩ := Option.bind_eq_some_iff.mp run
  obtain ⟨ss, hs, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨block, hb, out⟩ := Option.bind_eq_some_iff.mp rest
  cases Option.some.inj out
  exact ⟨row, block, hr, hs, hb, rfl⟩

theorem native_prefix_rowAt {a b : Pattern} {r : Nat} {sources : List Nat}
    (run : native a r = some (b, sources)) {i : Nat} (before : i < r) : rowAt b i = rowAt a i := by
  obtain ⟨row, block, hr, _, _, out⟩ := native_decomposition run
  subst b
  by_cases zero : i = 0
  · subst i; simp [rowAt]
  have bounds := rowAt_bounds hr
  have index : i - 1 < (a.take (r - 1)).length := by simp; omega
  simp [rowAt, zero, List.append_assoc, List.getElem?_append_left index, show i - 1 < r - 1 by omega]

theorem native_suffix_rowAt {a b : Pattern} {r i : Nat} {sources : List Nat}
    (run : native a r = some (b, sources)) (after : r < i) :
    rowAt b (i + sources.length) = (rowAt a i).map (Row.shiftAfter r sources.length) := by
  obtain ⟨row, block, hr, _, hb, out⟩ := native_decomposition run
  subst b
  have bounds := rowAt_bounds hr
  have front : (a.take (r - 1)).length = r - 1 := by simp; omega
  have length := nativeBlock_length hb
  have retained : (a.take (r - 1) ++ block).length = r + sources.length := by
    simp only [List.length_append, front, length]; omega
  simp only [rowAt, show i + sources.length ≠ 0 by omega, show i ≠ 0 by omega, if_false]
  rw [List.getElem?_append_right (by omega : (a.take (r - 1) ++ block).length ≤ i + sources.length - 1)]
  have align : i + sources.length - 1 - (a.take (r - 1) ++ block).length = i - 1 - r := by omega
  rw [align]
  simp only [List.getElem?_map, List.getElem?_drop]
  have align' : r + (i - 1 - r) = i - 1 := by omega
  rw [align']

theorem native_family_rowAt {a b : Pattern} {r j : Nat} {row : Row} {sources : List Nat} {block : Pattern}
    (hr : rowAt a r = some row) (run : native a r = some (b, sources))
    (blockRun : nativeBlock row r sources = some block) (bound : j < block.length) :
    rowAt b (r + j) = block[j]? := by
  obtain ⟨actualRow, actualBlock, atRow, _, atBlock, out⟩ := native_decomposition run
  have rowSame := Option.some.inj (atRow.symm.trans hr)
  subst actualRow
  have blockSame := Option.some.inj (atBlock.symm.trans blockRun)
  subst actualBlock; subst b
  have bounds := rowAt_bounds hr
  have front : (a.take (r - 1)).length = r - 1 := by simp; omega
  simp only [rowAt, show r + j ≠ 0 by omega, if_false, List.append_assoc]
  rw [List.getElem?_append_right (by omega : (a.take (r - 1)).length ≤ r + j - 1)]
  have align : r + j - 1 - (a.take (r - 1)).length = j := by omega
  rw [align, List.getElem?_append_left bound]

end IBLP
