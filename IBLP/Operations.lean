import IBLP.Trace

/-! 原始有限运行规则。纯列表操作参考 FullMarkedBLP/Native.lean，
但零项、全尾复制、三类筛选及展开调度按本 IBLP 主稿单独实现。 -/
namespace IBLP

def insertColumn (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x < y then x :: y :: ys else if x = y then y :: ys
    else y :: insertColumn x ys

def canonicalColumns (xs : List Nat) : List Nat := xs.foldr insertColumn []

/-- 正文 (2.5)，尾部没有旧 BLP 的 e 上界。 -/
def copyEntry (n : Nat) (last : Row) (x : Nat) : Option Nat := do
  let a ← last.columns.head?
  let p ← last.p
  if x < a then some x
  else if p ≤ x then some (x + (n - p))
  else do
    let pair ← (last.columns.zip (last.columns.drop last.step)).find? (fun pair => pair.1 == x)
    pure pair.2

/-- 只有高位交叉分支使用下一源列筛选。 -/
def keepCopiedMark (a : Pattern) (last : Row) (source : Nat)
    (row : Row) (copied : List Nat) (y : Nat) : Bool :=
  match last.columns.head?, last.p, markTrace a source y with
  | some minimum, some p, some trace =>
    match fromRight trace 2 with
    | none => false
    | some bottom =>
      if p ≤ bottom then true
      else match trace.find? (· < p) with
      | none => false
      | some u =>
        if u < minimum then true
        else match copyEntry a.length last u, copyEntry a.length last y with
        | some v, some image =>
          if v ∈ last.marks then
            let k := copied.idxOf image
            if row.step ≤ k + 1 then
              (copied[k + 1 - row.step]?).any (· ≤ minimum)
            else true
          else false
        | _, _ => false
  | _, _, _ => false

def copyRow (a : Pattern) (last : Row) (r : Nat) : Option Row := do
  let row ← rowAt a r
  let cols ← row.columns.mapM (copyEntry a.length last)
  let cols := canonicalColumns cols
  let kept := row.marks.filter (fun y => y ∈ row.columns && keepCopiedMark a last r row cols y)
  let marks ← kept.mapM (copyEntry a.length last)
  pure ⟨cols, row.step, canonicalColumns marks⟩

def rawCopy (a : Pattern) : Option Pattern := do
  let last ← a.getLast?
  let p ← last.p
  let tail ← ((List.range (a.length - p + 1)).map (p + ·)).mapM (copyRow a last)
  pure (a.take (a.length - 1) ++ tail)

def rawCopies : Nat → Pattern → Option Pattern
  | 0, a => some a
  | n + 1, a => (rawCopy a).bind (rawCopies n)

def nativeSourcesFuel (a : Pattern) (p : Nat) : Nat → Nat → Option (List Nat)
  | 0, _ => none
  | fuel + 1, u => do
    let q ← penultimate a u
    if p < q then
      let tail ← nativeSourcesFuel a p fuel q
      pure (q :: tail)
    else pure []

/-- 原生来源保留 q 阶梯的递减次序。 -/
def nativeSources (a : Pattern) (r : Nat) : Option (List Nat) := do
  let row ← rowAt a r
  if 2 * row.step < row.columns.length then some []
  else do
    let p ← row.p
    let e ← row.e
    nativeSourcesFuel a p (e + 1) e

def shiftAfter (r h x : Nat) : Nat := if r < x then x + h else x

def Row.shiftAfter (r h : Nat) (row : Row) : Row :=
  ⟨row.columns.map (IBLP.shiftAfter r h), row.step,
    row.marks.map (IBLP.shiftAfter r h)⟩

def nativeTop (row : Row) (r : Nat) (sources : List Nat) : Row :=
  let h := sources.length
  let targets := (List.range h).map (fun j => r + 1 + j)
  let marks := (row.marks ++ (List.range h).map (r + ·)).filter
    (fun x => x != r + h && !sources.contains x)
  ⟨canonicalColumns (row.columns ++ sources ++ targets), row.step + h, canonicalColumns marks⟩

/-- 两个删除对象从原行读取；中行例外只作用于第一次下降。 -/
def nativeLower (row : Row) (owner : Nat) (mediumException : Bool) : Option Row :=
  if mediumException then
    some ⟨row.columns.erase owner, row.step, row.marks.erase (owner - 1)⟩
  else do
    let e ← row.e
    pure ⟨(row.columns.erase owner).erase e, row.step - 1, row.marks.erase (owner - 1)⟩

def nativeBlockDown : Nat → Nat → Bool → Row → Option (List Row)
  | 0, _, _, top => some [top]
  | remaining + 1, owner, medium, top => do
    let lower ← nativeLower top owner medium
    let earlier ← nativeBlockDown remaining (owner - 1) false lower
    pure (earlier ++ [top])

def nativeBlock (row : Row) (r : Nat) (sources : List Nat) : Option (List Row) :=
  if sources.isEmpty then some [row]
  else nativeBlockDown sources.length (r + sources.length)
    (row.columns.length == 2 * row.step) (nativeTop row r sources)

def native (a : Pattern) (r : Nat) : Option (Pattern × List Nat) := do
  let row ← rowAt a r
  let sources ← nativeSources a r
  let block ← nativeBlock row r sources
  pure (a.take (r - 1) ++ block ++ (a.drop r).map (Row.shiftAfter r sources.length), sources)

abbrev Records := List (Nat × List Nat)
def recordAt (rec : Records) (r : Nat) : Option (List Nat) :=
  (rec.find? (fun entry => entry.1 == r)).map Prod.snd

/-- 去掉终点以后检查相邻因子，因此不检查底因子到最终源的箭头。 -/
def internalCheck (a : Pattern) (trace : List Nat) : Bool :=
  let factors := trace.dropLast
  (factors.zip factors.tail).all fun (u, v) =>
    (rowAt a u).any (fun row => row.columns.contains (v + 1))

def completionRecord (a : Pattern) (rec : Records) (r b : Nat) : Option (List Nat) := do
  let trace ← markTrace a r b
  let bottom ← fromRight trace 2
  let sources ← recordAt rec bottom
  if sources.isEmpty then none else if internalCheck a trace then some sources else none

def completeMarkRow (row : Row) (b : Nat) (sources : List Nat) : Row :=
  let targets := (List.range sources.length).map (fun j => b + 1 + j)
  ⟨canonicalColumns (row.columns ++ sources ++ targets), row.step + sources.length,
    canonicalColumns (row.marks.filter (fun x => !sources.contains x) ++ targets)⟩

def completeMark (a : Pattern) (rec : Records) (r b : Nat) : Pattern :=
  match rowAt a r, completionRecord a rec r b with
  | some row, some sources => a.set (r - 1) (completeMarkRow row b sources)
  | _, _ => a

def completeFrozenMarks (a : Pattern) (rec : Records) (r : Nat) : Pattern :=
  match rowAt a r with
  | none => a
  | some row => (canonicalColumns (row.marks.filter (· ∈ row.columns))).foldl
      (fun current b => completeMark current rec r b) a

/-- fuel 计入口旧行；生成的整个家族跳过。充分性由长度定理证明。 -/
def scanFuel : Nat → Pattern → Records → Nat → Option Pattern
  | 0, a, _, r => if a.length < r then some a else none
  | fuel + 1, a, rec, r =>
    if a.length < r then some a else do
      let marked := completeFrozenMarks a rec r
      let (next, sources) ← native marked r
      let nextRec := if sources.isEmpty then rec else (r, sources) :: rec
      scanFuel fuel next nextRec (r + sources.length + 1)

def scan (a : Pattern) (start : Nat) : Option Pattern :=
  scanFuel (a.length + 1 - start) a [] start

/-- 只有首次复制失败回退；任意后续复制成功性是单独的证明义务。 -/
def expand (a : Pattern) (m : Nat) : Option Pattern :=
  if a.isEmpty then none
  else if m = 0 ∨ isSuccessor a then cut a
  else match rawCopy a with
  | none => cut a
  | some first => do
    let copied ← rawCopies (m - 1) first
    let truncated ← cut copied
    scan truncated a.length

def Child (child parent : Pattern) : Prop := ∃ m, expand parent m = some child

inductive Reachable : Pattern → Prop
  | root : Reachable root
  | step {parent child : Pattern} : Reachable parent → Child child parent → Reachable child

theorem expand_zero (m : Nat) : expand zero m = none := rfl
theorem zero_no_child (a : Pattern) : ¬ Child a zero := by
  rintro ⟨m, h⟩
  simp [expand_zero] at h

theorem expand_parameter_zero (a : Pattern) : expand a 0 = cut a := by
  unfold expand cut
  split <;> simp_all

theorem root_rawCopy : rawCopy root = some
    [⟨[0,1],1,[]⟩, ⟨[0,1,2],1,[]⟩, ⟨[0,1,2,3],2,[]⟩,
     ⟨[2,3,4],1,[]⟩, ⟨[2,3,4,5],2,[]⟩,
     ⟨[2,3,5,6],2,[]⟩, ⟨[5,6,7],1,[]⟩] := by decide

theorem root_expand_one : expand root 1 = some
    [⟨[0,1],1,[]⟩, ⟨[0,1,2],1,[]⟩, ⟨[0,1,2,3],2,[]⟩,
     ⟨[2,3,4],1,[]⟩, ⟨[2,3,4,5],2,[]⟩,
     ⟨[2,3,4,5,6],3,[]⟩, ⟨[2,3,4,5,6,7],3,[6]⟩] := by decide

end IBLP
