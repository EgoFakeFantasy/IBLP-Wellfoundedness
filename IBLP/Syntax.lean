import Mathlib.Data.List.Pairwise
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-! 原 IBLP 的字面对象。行号为一基，List 位置为零基。
行型、proper 标记和语义证书是待证不变量，不作为运行时过滤器。 -/
namespace IBLP

structure Row where
  columns : List Nat
  step : Nat
  marks : List Nat
  deriving DecidableEq, Repr

abbrev Pattern := List Row

def rowAt (a : Pattern) (r : Nat) : Option Row :=
  if r = 0 then none else a[r - 1]?

/-- 倒数第 k 项；k=0 或超过长度时未定义。 -/
def fromRight (xs : List Nat) (k : Nat) : Option Nat :=
  if 0 < k ∧ k ≤ xs.length then xs[xs.length - k]? else none

def Row.p (row : Row) : Option Nat := fromRight row.columns (row.step + 1)
def Row.e (row : Row) : Option Nat := fromRight row.columns row.step
def Row.q (row : Row) : Option Nat := fromRight row.columns 2

def predecessor (a : Pattern) (r : Nat) : Option Nat := (rowAt a r).bind Row.p
def penultimate (a : Pattern) (r : Nat) : Option Nat := (rowAt a r).bind Row.q

/-- 只表达原始数组和标记的有限语法。 -/
def Row.BasicValid (r : Nat) (row : Row) : Prop :=
  row.columns.Pairwise (· < ·) ∧ 2 ≤ row.columns.length ∧
  row.columns.getLast? = some r ∧ ∀ b ∈ row.marks, b ∈ row.columns

def BasicValid (a : Pattern) : Prop :=
  ∀ r row, rowAt a r = some row → row.BasicValid r

/-- 正文 (2.2)，须由根和原展开保持性推得。 -/
def Row.OrdinaryShape (row : Row) : Prop :=
  (row.columns.length = 3 ∧ row.step = 1) ∨
  (row.columns.length = 2 * row.step ∧ 1 ≤ row.step) ∨
  (row.columns.length = 2 * row.step - 1 ∧ 3 ≤ row.step)

def OrdinaryShape (a : Pattern) : Prop :=
  ∀ row ∈ a, row.OrdinaryShape

/-- 正文 (2.3) 改写为零基位置；标记不含末点，源位置不为零。 -/
def Row.ProperMark (row : Row) (b : Nat) : Prop :=
  ∃ k, row.columns[k]? = some b ∧ row.step + 1 ≤ k ∧ k + 1 < row.columns.length

def ProperMarks (a : Pattern) : Prop :=
  ∀ row ∈ a, ∀ b ∈ row.marks, row.ProperMark b

def Saturated (a : Pattern) : Prop :=
  ∀ r row p e q, rowAt a r = some row → row.p = some p → row.e = some e →
    penultimate a e = some q → q ≤ p

def zero : Pattern := []

/-- 主稿定理 1.1 的六行根，全部标记为空。 -/
def root : Pattern :=
  [⟨[0, 1], 1, []⟩, ⟨[0, 1, 2], 1, []⟩,
   ⟨[0, 1, 2, 3], 2, []⟩, ⟨[2, 3, 4], 1, []⟩,
   ⟨[2, 3, 4, 5], 2, []⟩, ⟨[4, 5, 6], 1, []⟩]

/-- 零图案无边；任意非零图案的零参数操作删除末行。 -/
def cut (a : Pattern) : Option Pattern :=
  if a.isEmpty then none else some a.dropLast

def isSuccessor (a : Pattern) : Bool :=
  match a.getLast? with
  | none => false
  | some row => row.columns.length == 2 && row.columns.head? == some 0

theorem rowAt_zero (a : Pattern) : rowAt a 0 = none := by simp [rowAt]

theorem rowAt_pos {a : Pattern} {r : Nat} {row : Row}
    (h : rowAt a r = some row) : 0 < r := by
  by_contra hn
  have hr : r = 0 := by omega
  simp [hr, rowAt] at h

theorem rowAt_le_length {a : Pattern} {r : Nat} {row : Row}
    (h : rowAt a r = some row) : r ≤ a.length := by
  have hr := rowAt_pos h
  have hg : a[r - 1]? = some row := by simpa [rowAt, Nat.ne_of_gt hr] using h
  have hlt : r - 1 < a.length := (List.getElem?_eq_some_iff.mp hg).1
  omega

theorem root_length : root.length = 6 := rfl
theorem root_nonzero : root ≠ zero := by decide
theorem zero_cut : cut zero = none := rfl
theorem zero_not_successor : isSuccessor zero = false := rfl
theorem root_not_successor : isSuccessor root = false := by decide

theorem root_predecessors : root.map Row.p =
    [some 0, some 1, some 1, some 3, some 3, some 5] := by decide

theorem root_endpoints : root.map Row.e =
    [some 1, some 2, some 2, some 4, some 4, some 6] := by decide

theorem root_shapes : OrdinaryShape root := by
  intro row h
  simp only [root, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h <;> subst row <;> simp [Row.OrdinaryShape]

theorem root_marks_empty : ∀ row ∈ root, row.marks = [] := by
  intro row h
  simp only [root, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h <;> subst row <;> rfl

theorem root_proper : ProperMarks root := by
  intro row hr b hb
  rw [root_marks_empty row hr] at hb
  contradiction

theorem root_valid : BasicValid root := by
  intro r row h
  have hp := rowAt_pos h
  have hle : r ≤ 6 := rowAt_le_length h
  interval_cases r <;> norm_num [rowAt, root] at h <;> subst row <;>
    simp [Row.BasicValid]

theorem root_saturated : Saturated root := by
  intro r row p e q hr hp he hq
  have hpos := rowAt_pos hr
  have hle : r ≤ 6 := rowAt_le_length hr
  interval_cases r <;> norm_num [rowAt, root] at hr <;> subst row <;>
    norm_num [Row.p, Row.e, fromRight] at hp he <;> subst p <;> subst e <;>
    norm_num [penultimate, rowAt, root, Row.q, fromRight] at hq <;> omega

end IBLP
