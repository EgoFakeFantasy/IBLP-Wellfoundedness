import IBLP.NativeTraceShift
import FullMarkedBLP.NativeBTransport

namespace IBLP

/-- The original native operation transports every old q, including the
expanded base row. The newly generated positive family rows are separate. -/
theorem native_penultimate_shift {a b : Pattern} (valid : BasicValid a) (shapes : OrdinaryShape a)
    {owner i q : Nat} {row : Row} {sources : List Nat} (run : native a owner = some (b, sources))
    (atRow : rowAt a i = some row) (hq : row.q = some q) :
    penultimate b (shiftAfter owner sources.length i) = some (shiftAfter owner sources.length q) := by
  have atEncoded : FullMarkedBLP.rowAt (NativeBridge.encode a) i = some (NativeBridge.encodeRow row) := by
    simp only [NativeBridge.rowAt_encode, atRow, Option.map_some]
  have result := FullMarkedBLP.native_b_shift (NativeBridge.valid_encode valid shapes)
    (NativeBridge.encoded_native run) atEncoded hq
  simpa only [NativeBridge.rowAt_encode, Option.bind_map, NativeBridge.encode_q, penultimate] using result

theorem native_base_q {a b : Pattern} (valid : BasicValid a) (shapes : OrdinaryShape a)
    {owner q : Nat} {row : Row} {sources : List Nat} (run : native a owner = some (b, sources))
    (atRow : rowAt a owner = some row) (hq : row.q = some q) : penultimate b owner = some q := by
  have below : q < owner := penultimate_lt valid (by simp [penultimate, atRow, hq])
  simpa only [shiftAfter, if_neg (Nat.lt_irrefl owner), if_neg (by omega : ¬ owner < q)] using
    native_penultimate_shift valid shapes run atRow hq

end IBLP
