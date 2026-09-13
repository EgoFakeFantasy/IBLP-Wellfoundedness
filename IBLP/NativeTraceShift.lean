import IBLP.NativePrefixTrace
import FullMarkedBLP.NativeTraceShift

namespace IBLP.NativeBridge

@[simp] theorem predecessor_encode (a : IBLP.Pattern) (r : Nat) :
    FullMarkedBLP.predecessor (encode a) r = IBLP.predecessor a r := by
  cases hr : IBLP.rowAt a r <;>
    simp [FullMarkedBLP.predecessor, IBLP.predecessor, hr, Bind.bind, Option.bind]

theorem encoded_native {a b : IBLP.Pattern} {r : Nat} {sources : List Nat}
    (run : IBLP.native a r = some (b, sources)) :
    FullMarkedBLP.native (encode a) r = some (encode b, sources) := by
  rw [native_encode, run]
  rfl

end IBLP.NativeBridge

namespace IBLP

theorem shiftAfter_strictMono (r h : Nat) : StrictMono (shiftAfter r h) := by
  intro x y less
  unfold shiftAfter
  split <;> split <;> omega

/-- Includes the old base row: its p is the bottom family's retained p. -/
theorem native_predecessor_shift {a b : Pattern} (valid : BasicValid a) (shapes : OrdinaryShape a)
    {r i q : Nat} {sources : List Nat} (run : native a r = some (b, sources))
    (pred : predecessor a i = some q) :
    predecessor b (shiftAfter r sources.length i) = some (shiftAfter r sources.length q) := by
  have encodedPred : FullMarkedBLP.predecessor (NativeBridge.encode a) i = some q := by simpa using pred
  have shifted := FullMarkedBLP.native_predecessor_shift (NativeBridge.valid_encode valid shapes)
    (NativeBridge.encoded_native run) encodedPred
  simpa only [NativeBridge.predecessor_encode] using shifted

theorem FactorTrace.native_shift {a b : Pattern} (valid : BasicValid a) (shapes : OrdinaryShape a)
    {r target start : Nat} {sources rows : List Nat} (run : native a r = some (b, sources))
    (h : FactorTrace a target start rows) :
    FactorTrace b (shiftAfter r sources.length target) (shiftAfter r sources.length start)
      (rows.map (shiftAfter r sources.length)) := by
  induction h with
  | single hp hn => exact .single (native_predecessor_shift valid shapes run hp) (shiftAfter_strictMono _ _ hn)
  | cons hp hn inner ih => exact .cons (native_predecessor_shift valid shapes run hp) (shiftAfter_strictMono _ _ hn) ih

theorem Trace.native_shift {a b : Pattern} (valid : BasicValid a) (shapes : OrdinaryShape a)
    {r target start : Nat} {sources rows : List Nat} (run : native a r = some (b, sources))
    (h : Trace a target start rows) :
    Trace b (shiftAfter r sources.length target) (shiftAfter r sources.length start)
      (rows.map (shiftAfter r sources.length)) := by
  induction h with
  | done => exact .done
  | step ht hp hn inner ih =>
    exact .step (shiftAfter_strictMono _ _ ht) (native_predecessor_shift valid shapes run hp)
      (shiftAfter_strictMono _ _ hn) ih

end IBLP
