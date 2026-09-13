import IBLP.Columns
import FullMarkedBLP.Native

/-! Exact data translation for the identical native list program at the
fixed FullMarkedBLP revision. This does not translate copy, cut, expansion,
roots, the stronger IBLP shape/proper invariants, or semantic certificates. -/
namespace IBLP.NativeBridge

def encodeRow (row : IBLP.Row) : FullMarkedBLP.Row := ⟨row.columns, row.step, row.marks⟩
def decodeRow (row : FullMarkedBLP.Row) : IBLP.Row := ⟨row.core, row.step, row.marks⟩
def encode (a : IBLP.Pattern) : FullMarkedBLP.Pattern := a.map encodeRow

@[simp] theorem decode_encode (row : IBLP.Row) : decodeRow (encodeRow row) = row := rfl
@[simp] theorem encode_decode (row : FullMarkedBLP.Row) : encodeRow (decodeRow row) = row := rfl
theorem encodeRow_injective : Function.Injective encodeRow := fun _ _ h => congrArg decodeRow h

@[simp] theorem rowAt_encode (a : IBLP.Pattern) (r : Nat) :
    FullMarkedBLP.rowAt (encode a) r = (IBLP.rowAt a r).map encodeRow := by
  simp only [FullMarkedBLP.rowAt, IBLP.rowAt, encode, List.getElem?_map]
  split <;> rfl

@[simp] theorem encode_p (row : IBLP.Row) : (encodeRow row).p = row.p := rfl
@[simp] theorem encode_e (row : IBLP.Row) : (encodeRow row).e = row.e := rfl
@[simp] theorem encode_q (row : IBLP.Row) : (encodeRow row).b = row.q := rfl
@[simp] theorem encode_columns (row : IBLP.Row) : (encodeRow row).core = row.columns := rfl
@[simp] theorem encode_step (row : IBLP.Row) : (encodeRow row).step = row.step := rfl

theorem nativeSourcesFuel_encode (a : IBLP.Pattern) (p fuel u : Nat) :
    FullMarkedBLP.nativeSourcesFuel (encode a) p fuel u = IBLP.nativeSourcesFuel a p fuel u := by
  induction fuel generalizing u with
  | zero => rfl
  | succ fuel ih =>
    cases hr : IBLP.rowAt a u with
    | none => simp [FullMarkedBLP.nativeSourcesFuel, IBLP.nativeSourcesFuel, IBLP.penultimate, hr]
    | some row =>
      simp only [FullMarkedBLP.nativeSourcesFuel, IBLP.nativeSourcesFuel, IBLP.penultimate,
        rowAt_encode, hr, Option.map_some, Bind.bind, Option.bind, encode_q]
      cases hq : row.q with
      | none => rfl
      | some q => simp only [ih]

theorem nativeSources_encode (a : IBLP.Pattern) (r : Nat) :
    FullMarkedBLP.nativeSources (encode a) r = IBLP.nativeSources a r := by
  cases hr : IBLP.rowAt a r with
  | none => simp [FullMarkedBLP.nativeSources, IBLP.nativeSources, hr]
  | some row =>
    simp only [FullMarkedBLP.nativeSources, IBLP.nativeSources, rowAt_encode, hr,
      Option.map_some, Bind.bind, Option.bind, encode_p, encode_e, encode_columns, encode_step]
    split
    · rfl
    · cases hp : row.p with
      | none => rfl
      | some p =>
        cases he : row.e with
        | none => rfl
        | some e => exact nativeSourcesFuel_encode a p (e + 1) e

@[simp] theorem nativeTop_encode (row : IBLP.Row) (r : Nat) (sources : List Nat) :
    FullMarkedBLP.nativeTop (encodeRow row) r sources = encodeRow (IBLP.nativeTop row r sources) := by
  simp only [FullMarkedBLP.nativeTop, IBLP.nativeTop, encodeRow, IBLP.canonicalColumns_eq_upstream]

@[simp] theorem shiftRow_encode (row : IBLP.Row) (r h : Nat) :
    FullMarkedBLP.Row.shiftAfter r h (encodeRow row) = encodeRow (IBLP.Row.shiftAfter r h row) := rfl

theorem nativeLower_encode (row : IBLP.Row) (owner : Nat) (medium : Bool) :
    FullMarkedBLP.nativeLower (encodeRow row) owner medium =
      (IBLP.nativeLower row owner medium).map encodeRow := by
  cases medium with
  | true => rfl
  | false =>
    simp only [FullMarkedBLP.nativeLower, IBLP.nativeLower, Bool.false_eq_true, ↓reduceIte, encode_e]
    cases he : row.e <;> rfl

theorem nativeBlockDown_encode (count owner : Nat) (medium : Bool) (row : IBLP.Row) :
    FullMarkedBLP.nativeBlockDown count owner medium (encodeRow row) =
      (IBLP.nativeBlockDown count owner medium row).map encode := by
  induction count generalizing owner medium row with
  | zero => rfl
  | succ count ih =>
    simp only [FullMarkedBLP.nativeBlockDown, IBLP.nativeBlockDown, nativeLower_encode]
    cases hl : IBLP.nativeLower row owner medium with
    | none => rfl
    | some lower =>
      simp only [Option.map_some, Bind.bind, Option.bind, ih]
      cases hb : IBLP.nativeBlockDown count (owner - 1) false lower with
      | none => rfl
      | some block =>
        change some (encode block ++ [encodeRow row]) = some (encode (block ++ [row]))
        simp only [encode, List.map_append, List.map_singleton]

theorem nativeBlock_encode (row : IBLP.Row) (r : Nat) (sources : List Nat) :
    FullMarkedBLP.nativeBlock (encodeRow row) r sources = (IBLP.nativeBlock row r sources).map encode := by
  simp only [FullMarkedBLP.nativeBlock, IBLP.nativeBlock, nativeTop_encode]
  split
  · rfl
  · exact nativeBlockDown_encode _ _ _ _

theorem native_encode (a : IBLP.Pattern) (r : Nat) :
    FullMarkedBLP.native (encode a) r =
      (IBLP.native a r).map (fun result => (encode result.1, result.2)) := by
  simp only [FullMarkedBLP.native, IBLP.native, rowAt_encode, nativeSources_encode]
  cases hr : IBLP.rowAt a r with
  | none => rfl
  | some row =>
    simp only [Option.map_some, Bind.bind, Option.bind]
    cases hs : IBLP.nativeSources a r with
    | none => rfl
    | some sources =>
      simp only [nativeBlock_encode]
      cases hb : IBLP.nativeBlock row r sources with
      | none => rfl
      | some block =>
        change some ((encode a).take (r - 1) ++ encode block ++
          ((encode a).drop r).map (FullMarkedBLP.Row.shiftAfter r sources.length), sources) =
          some (encode (a.take (r - 1) ++ block ++ (a.drop r).map (IBLP.Row.shiftAfter r sources.length)), sources)
        simp only [encode, List.map_append,
          List.map_take, List.map_drop, List.map_map]
        rfl

end IBLP.NativeBridge
