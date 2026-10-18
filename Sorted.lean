import Mathlib.Tactic.IntervalCases

/-- Sortedness. -/
def Sorted (a : Array Nat) : Prop :=
  ∀ i j (hi : i < a.size) (hj : j < a.size), i ≤ j → a[i] ≤ a[j]

/-- A witnessing inversion shows an array is not sorted. -/
theorem not_sorted_of_lt {a : Array Nat} {i j : Nat} (hi : i < a.size) (hj : j < a.size)
    (hij : i ≤ j) (h : a[j] < a[i]) : ¬ Sorted a :=
  fun hs => absurd (hs i j hi hj hij) (Nat.not_le.mpr h)

/-- Proves `Sorted` for a concrete array by exhausting all index pairs. -/
local macro "sorted_by_cases" : tactic =>
  `(tactic| (intro i j hi hj hij; simp at hi hj <;>
    first | (interval_cases i <;> interval_cases j <;> simp_all) | simp_all))

/-- Proves `¬ Sorted a` for a concrete array from an inversion at indices `i ≤ j`. -/
local macro "not_sorted_at " i:term:max j:term:max : term =>
  `(not_sorted_of_lt (i := $i) (j := $j) (by simp) (by simp) (by decide) (by decide))

/-! Examples of `Sorted`, following ZOMBIES
(Zero, One, Many, Boundaries, Interfaces, Exceptions, Simple scenarios). -/

-- Zero: the empty array is vacuously sorted.
example : Sorted #[] := by sorted_by_cases

-- One: a singleton is sorted.
example : Sorted #[42] := by sorted_by_cases

-- Many: a strictly increasing array is sorted.
example : Sorted #[1, 3, 5, 7, 9, 11] := by sorted_by_cases

-- Boundaries: duplicates (non-strict) are sorted; equal elements throughout.
example : Sorted #[2, 2, 2] := by sorted_by_cases
example : Sorted #[1, 1, 2, 3, 3] := by sorted_by_cases

-- Exceptions: unsorted arrays are not sorted.
example : ¬ Sorted #[3, 1, 2] := not_sorted_at 0 1
example : ¬ Sorted #[1, 2, 3, 2] := not_sorted_at 2 3
