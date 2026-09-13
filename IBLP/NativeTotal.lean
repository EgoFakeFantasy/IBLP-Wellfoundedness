import IBLP.NativeSyntaxBridge
import IBLP.NativeTermination
import FullMarkedBLP.NativeBlockActual

namespace IBLP

namespace NativeBridge

/-- The original three shape alternatives imply the upstream array premise;
the converse is not used, since that premise also allows other long rows. -/
theorem shape_encode {row : IBLP.Row} (shape : row.OrdinaryShape) : (encodeRow row).OrdinaryShape := by
  simp only [FullMarkedBLP.Row.OrdinaryShape, encodeRow]
  rcases shape with shape | shape | shape <;> omega

theorem valid_encode {a : IBLP.Pattern} (valid : BasicValid a) (shapes : OrdinaryShape a) :
    ∀ r row, FullMarkedBLP.rowAt (encode a) r = some row → row.CoreValid r := by
  intro r row hr
  rw [rowAt_encode] at hr
  obtain ⟨old, atOld, same⟩ := Option.map_eq_some_iff.mp hr
  subst row
  have hv := valid _ _ atOld
  exact ⟨hv.1, hv.2.1, hv.2.2.1, shape_encode (shapes old (rowAt_mem atOld))⟩

end NativeBridge

/-- The literal native program, including every descent of its new family,
is defined on every valid original row. This is stronger than source-walk
termination and does not assume that any semantic certificates exist. -/
theorem native_total {a : Pattern} (valid : BasicValid a) (shapes : OrdinaryShape a)
    {r : Nat} {row : Row} (hr : rowAt a r = some row) : ∃ b sources, native a r = some (b, sources) := by
  have encodedRow : FullMarkedBLP.rowAt (NativeBridge.encode a) r = some (NativeBridge.encodeRow row) := by
    simp only [NativeBridge.rowAt_encode, hr, Option.map_some]
  obtain ⟨b, sources, run⟩ := FullMarkedBLP.native_total (NativeBridge.valid_encode valid shapes) encodedRow
  rw [NativeBridge.native_encode] at run
  obtain ⟨result, computed, _⟩ := Option.map_eq_some_iff.mp run
  exact ⟨result.1, result.2, computed⟩

theorem nativeSources_decreasing {a : Pattern} (valid : BasicValid a)
    {r : Nat} {sources : List Nat} (run : nativeSources a r = some sources) : sources.Pairwise (· > ·) := by
  obtain ⟨row, _, run⟩ := Option.bind_eq_some_iff.mp run
  split at run
  · cases Option.some.inj run
    exact .nil
  · obtain ⟨p, _, run⟩ := Option.bind_eq_some_iff.mp run
    obtain ⟨e, _, run⟩ := Option.bind_eq_some_iff.mp run
    exact nativeSourcesFuel_decreasing valid run

theorem nativeSources_disjoint {a : Pattern} (valid : BasicValid a) (shapes : OrdinaryShape a)
    {r : Nat} {row : Row} {sources : List Nat} (hr : rowAt a r = some row)
    (run : nativeSources a r = some sources) : ∀ x ∈ sources, x ∉ row.columns := by
  have encodedRow : FullMarkedBLP.rowAt (NativeBridge.encode a) r = some (NativeBridge.encodeRow row) := by
    simp only [NativeBridge.rowAt_encode, hr, Option.map_some]
  exact FullMarkedBLP.nativeSources_disjoint (NativeBridge.valid_encode valid shapes) encodedRow
    ((NativeBridge.nativeSources_encode a r).trans run)

end IBLP
