module

public import BinarySearch.Defs
public import Mathlib.Analysis.Asymptotics.Basic
public import Mathlib.Data.Nat.Log

/-! Formal recursive-call cost bounds for binary search. -/

@[expose] public section

/-- Worst-case number of calls to `go` on an interval of length `n`.

Each call counts once, then takes the more expensive of the two recursive
subranges, whose lengths are `n / 2` and `(n - 1) / 2`. -/
def binarySearchCalls : Nat → Nat
  | 0 => 1
  | n + 1 => 1 + max (binarySearchCalls ((n + 1) / 2)) (binarySearchCalls (n / 2))
termination_by n => n
decreasing_by all_goals omega

/-- A call count always includes at least one call. -/
theorem binarySearchCalls_pos (n : Nat) : 1 ≤ binarySearchCalls n := by
  cases n <;> simp [binarySearchCalls]

/-- Counts calls made by the actual search loop, including the initial call.

This cost model counts recursive calls; it treats the work within each call
(indexing and comparisons) as constant time. -/
def binarySearch.goCalls (a : Array Nat) (target lo hi : Nat) : Nat :=
  if h : lo < hi then
    let mid := lo + (hi - lo) / 2
    if hm : mid < a.size then
      let v := a[mid]
      if v == target then 1
      else if v < target then binarySearch.goCalls a target (mid + 1) hi + 1
      else binarySearch.goCalls a target lo mid + 1
    else 1
  else 1
termination_by hi - lo
decreasing_by all_goals omega

/-- The recursive-call count is bounded by the base-2 logarithm plus a constant. -/
theorem binarySearchCalls_le_log_add_two (n : Nat) :
    binarySearchCalls n ≤ Nat.log2 n + 2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          simp [binarySearchCalls]
      | succ n =>
          by_cases hn : n = 0
          · subst n
            norm_num [binarySearchCalls]
          · have hn' : 1 ≤ n := by omega
            have hleft : (n + 1) / 2 < n + 1 := by omega
            have hright : n / 2 < n + 1 := by omega
            have hchildLogNat :
                Nat.log 2 (n + 1) = Nat.log 2 ((n + 1) / 2) + 1 :=
              Nat.log_of_one_lt_of_le Nat.one_lt_two (by omega)
            have hchildLog : Nat.log2 ((n + 1) / 2) + 1 = Nat.log2 (n + 1) := by
              simpa only [← Nat.log2_eq_log_two] using hchildLogNat.symm
            have hleftLogNat :
                Nat.log 2 (n / 2) ≤ Nat.log 2 ((n + 1) / 2) :=
              Nat.log_mono_right (b := 2) (by omega)
            have hleftLog : Nat.log2 (n / 2) ≤ Nat.log2 ((n + 1) / 2) := by
              simpa only [← Nat.log2_eq_log_two] using hleftLogNat
            rw [binarySearchCalls]
            have hmax :
                max (binarySearchCalls ((n + 1) / 2)) (binarySearchCalls (n / 2)) ≤
                  Nat.log2 (n + 1) + 1 := by
              apply max_le
              · calc
                  binarySearchCalls ((n + 1) / 2) ≤ Nat.log2 ((n + 1) / 2) + 2 :=
                    ih _ hleft
                  _ = Nat.log2 (n + 1) + 1 := by omega
              · calc
                  binarySearchCalls (n / 2) ≤ Nat.log2 (n / 2) + 2 :=
                    ih _ hright
                  _ ≤ Nat.log2 (n + 1) + 1 := by omega
            omega

/-- Every concrete execution uses at most the calls given by the recurrence. -/
theorem binarySearch.goCalls_le_binarySearchCalls (a : Array Nat) (target : Nat) :
    ∀ lo hi, binarySearch.goCalls a target lo hi ≤ binarySearchCalls (hi - lo) := by
  intro lo hi
  induction lo, hi using binarySearch.go.induct a target with
  | case1 lo hi hlo mid hmid v heq =>
      rw [binarySearch.goCalls.eq_1]
      simp only [hlo, mid, hmid, v, heq, dite_eq_ite]
      exact binarySearchCalls_pos (hi - lo)
  | case2 lo hi hlo mid hmid v hne hlt ih =>
      cases hN : hi - lo with
      | zero =>
          omega
      | succ n =>
          have hmidEq : mid = lo + (n + 1) / 2 := by
            dsimp [mid]
            omega
          have hrightLen : hi - (lo + (n + 1) / 2 + 1) = n / 2 := by
            omega
          have hmidBound : lo + (n + 1) / 2 < a.size := by
            simpa [hmidEq] using hmid
          have hv : a[lo + (n + 1) / 2] = v := by
            simp [hmidEq, v]
          have hnotEq : ¬(a[lo + (n + 1) / 2] == target) = true := by
            simpa [hv] using hne
          have hlt' : a[lo + (n + 1) / 2] < target := by
            simpa [hv] using hlt
          rw [binarySearch.goCalls.eq_1]
          simp only [hlo, hN, hmidBound, hnotEq, hlt', dite_eq_ite, ge_iff_le,
            Bool.false_eq_true, ite_true, ite_false]
          have ih' :
              binarySearch.goCalls a target (mid + 1) hi ≤ binarySearchCalls (n / 2) := by
            simpa only [hmidEq, hrightLen] using ih
          rw [binarySearchCalls]
          have hchild :
              binarySearch.goCalls a target (mid + 1) hi ≤
                max (binarySearchCalls ((n + 1) / 2)) (binarySearchCalls (n / 2)) :=
            ih'.trans (Nat.le_max_right _ _)
          have hchild' :
              binarySearch.goCalls a target (lo + (n + 1) / 2 + 1) hi ≤
                max (binarySearchCalls ((n + 1) / 2)) (binarySearchCalls (n / 2)) := by
            simpa only [hmidEq] using hchild
          simpa only [Nat.add_comm] using Nat.add_le_add_left hchild' 1
  | case3 lo hi hlo mid hmid v hne hnotlt ih =>
      cases hN : hi - lo with
      | zero =>
          omega
      | succ n =>
          have hmidEq : mid = lo + (n + 1) / 2 := by
            dsimp [mid]
            omega
          have hleftLen : lo + (n + 1) / 2 - lo = (n + 1) / 2 := by
            omega
          have hmidBound : lo + (n + 1) / 2 < a.size := by
            simpa [hmidEq] using hmid
          have hv : a[lo + (n + 1) / 2] = v := by
            simp [hmidEq, v]
          have hnotEq : ¬(a[lo + (n + 1) / 2] == target) = true := by
            simpa [hv] using hne
          have hnotlt' : ¬a[lo + (n + 1) / 2] < target := by
            simpa [hv] using hnotlt
          rw [binarySearch.goCalls.eq_1]
          simp only [hlo, hN, hmidBound, hnotEq, hnotlt', dite_eq_ite, ge_iff_le,
            Bool.false_eq_true, ite_true, ite_false]
          have ih' :
              binarySearch.goCalls a target lo mid ≤
                binarySearchCalls ((n + 1) / 2) := by
            simpa only [hmidEq, hleftLen] using ih
          rw [binarySearchCalls]
          have hchild :
              binarySearch.goCalls a target lo mid ≤
                max (binarySearchCalls ((n + 1) / 2)) (binarySearchCalls (n / 2)) :=
            ih'.trans (Nat.le_max_left _ _)
          have hchild' :
              binarySearch.goCalls a target lo (lo + (n + 1) / 2) ≤
                max (binarySearchCalls ((n + 1) / 2)) (binarySearchCalls (n / 2)) := by
            simpa only [hmidEq] using hchild
          simpa only [Nat.add_comm] using Nat.add_le_add_left hchild' 1
  | case4 lo hi hlo mid hnotmid =>
      rw [binarySearch.goCalls.eq_1]
      simp only [hlo, mid, hnotmid, beq_iff_eq, dite_eq_ite]
      exact binarySearchCalls_pos (hi - lo)
  | case5 lo hi hnotlo =>
      rw [binarySearch.goCalls.eq_1]
      simp only [hnotlo, beq_iff_eq, dite_eq_ite]
      exact binarySearchCalls_pos (hi - lo)

/-- A shifted-logarithm bound, defined at zero as well as on positive inputs. -/
theorem binarySearchCalls_le_three_mul_log (n : Nat) :
    binarySearchCalls n ≤ 3 * Nat.log2 (n + 2) := by
  have hlog := binarySearchCalls_le_log_add_two n
  have hmonoNat : Nat.log 2 n ≤ Nat.log 2 (n + 2) :=
    Nat.log_mono_right (b := 2) (by omega)
  have hmono : Nat.log2 n ≤ Nat.log2 (n + 2) := by
    simpa only [← Nat.log2_eq_log_two] using hmonoNat
  have hpos : 1 ≤ Nat.log2 (n + 2) := by
    rw [Nat.log2_eq_log_two]
    exact Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt (Nat.log_pos Nat.one_lt_two (by omega)))
  omega

/-- On an array of size `n`, every concrete search uses `O(log n)` recursive calls. -/
theorem binarySearch.goCalls_le_three_mul_log (a : Array Nat) (target : Nat) :
    binarySearch.goCalls a target 0 a.size ≤ 3 * Nat.log2 (a.size + 2) := by
  calc
    binarySearch.goCalls a target 0 a.size ≤ binarySearchCalls a.size := by
      simpa using binarySearch.goCalls_le_binarySearchCalls a target 0 a.size
    _ ≤ 3 * Nat.log2 (a.size + 2) := binarySearchCalls_le_three_mul_log a.size

/-- The worst-case recursive-call count is asymptotically logarithmic. -/
theorem binarySearchCalls_isBigO :
    (fun n : Nat => (binarySearchCalls n : ℝ)) =O[Filter.atTop]
      (fun n => (Nat.log2 (n + 2) : ℝ)) := by
  apply Asymptotics.IsBigOWith.isBigO (c := 3)
  rw [Asymptotics.isBigOWith_iff]
  filter_upwards [Filter.Eventually.of_forall
    (fun n => binarySearchCalls_le_three_mul_log n)] with n h
  have hReal :
      (binarySearchCalls n : ℝ) ≤ 3 * (Nat.log2 (n + 2) : ℝ) := by
    exact_mod_cast h
  have hCallsNonneg : (0 : ℝ) ≤ (binarySearchCalls n : ℝ) := Nat.cast_nonneg _
  have hLogNonneg : (0 : ℝ) ≤ (Nat.log2 (n + 2) : ℝ) := Nat.cast_nonneg _
  simpa only [Real.norm_eq_abs, abs_of_nonneg hCallsNonneg, abs_of_nonneg hLogNonneg] using hReal
