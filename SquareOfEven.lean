import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Tactic.Ring

theorem square_of_even (n : Nat) (h : Even n) : Even (n ^ 2) := by
  rcases h with ⟨k, hk⟩
  subst hk
  refine ⟨k * (k + k), ?_⟩
  ring
