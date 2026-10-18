import Mathlib.Tactic.IntervalCases

/-- Sortedness. -/
def Sorted (a : Array Nat) : Prop :=
  ∀ i j (hi : i < a.size) (hj : j < a.size), i ≤ j → a[i] ≤ a[j]

/-! Examples of `Sorted`, following ZOMBIES
(Zero, One, Many, Boundaries, Interfaces, Exceptions, Simple scenarios). -/

-- Zero: the empty array is vacuously sorted.
example : Sorted #[] := by
  intro i j hi
  simp at hi

-- One: a singleton is sorted.
example : Sorted #[42] := by
  intro i j hi hj hij
  simp at hi hj
  subst hi; subst hj
  exact Nat.le_refl _

-- Many: a strictly increasing array is sorted.
example : Sorted #[1, 3, 5, 7, 9, 11] := by
  intro i j hi hj hij
  simp at hi hj
  interval_cases i <;> interval_cases j <;> simp_all

-- Boundaries: duplicates (non-strict) are sorted; equal elements throughout.
example : Sorted #[2, 2, 2] := by
  intro i j hi hj hij
  simp at hi hj
  interval_cases i <;> interval_cases j <;> simp_all

example : Sorted #[1, 1, 2, 3, 3] := by
  intro i j hi hj hij
  simp at hi hj
  interval_cases i <;> interval_cases j <;> simp_all

-- Exceptions: unsorted arrays are not sorted.
example : ¬ Sorted #[3, 1, 2] := by
  intro h
  have := h 0 1 (by simp) (by simp) (by decide)
  simp at this

example : ¬ Sorted #[1, 2, 3, 2] := by
  intro h
  have := h 2 3 (by simp) (by simp) (by decide)
  simp at this
