module

public import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Tactic.Ring

public section

theorem square_of_even (n : Nat) (h : Even n) : Even (n ^ 2) := by
  rcases h with ⟨k, hk⟩
  subst hk
  refine ⟨k * (k + k), ?_⟩
  ring
