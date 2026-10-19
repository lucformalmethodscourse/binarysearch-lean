module

public meta import BinarySearch.Defs

@[expose] public section

/-! Example invocations -/

#eval binarySearch #[1, 3, 5, 7, 9, 11] 7   -- some 3
#eval binarySearch #[1, 3, 5, 7, 9, 11] 1   -- some 0
#eval binarySearch #[1, 3, 5, 7, 9, 11] 11  -- some 5
#eval binarySearch #[1, 3, 5, 7, 9, 11] 4   -- none
#eval binarySearch #[1, 3, 5, 7, 9, 11] 100 -- none
#eval binarySearch #[] 5                    -- none
#eval binarySearch #[42] 42                 -- some 0

example : binarySearch #[1, 3, 5, 7, 9, 11] 7 = some 3 := by
  simp [binarySearch, binarySearch.go]
example : binarySearch #[1, 3, 5, 7, 9, 11] 4 = none := by
  simp [binarySearch, binarySearch.go]
