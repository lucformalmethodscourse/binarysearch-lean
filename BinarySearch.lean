module

public import Mathlib.Analysis.Asymptotics.Basic
public import Mathlib.Data.Nat.Log
public import Sorted

@[expose] public section

/-
Good choice of data structure: `Array Nat` (or `Array α` with `[Ord α]`).
- O(1) indexing, which binary search needs (`List` is O(n) per index).
- Bounds-proved indexing (`a[i]'h`) makes verification natural.
- Sortedness: ∀ i j, i ≤ j → a[i] ≤ a[j].
-/

/-- Binary search on a sorted array. Returns the index of `target`, if present.

Precondition (not enforced here): `a` is sorted, i.e.
`∀ i j (hi : i < a.size) (hj : j < a.size), i ≤ j → a[i] ≤ a[j]`.

Not enforcing it keeps the function total and executable on any input
(on unsorted input it may return `none` incorrectly, but never crashes).

The usual approach: keep the definition simple and state the precondition in
the correctness theorems, e.g.
`Sorted a → binarySearch a t = some i → a[i]? = some t` and
`Sorted a → t ∈ a → (binarySearch a t).isSome`. -/
def binarySearch (a : Array Nat) (target : Nat) : Option Nat :=
  go 0 a.size
where
  /-- Searches within the half-open range `[lo, hi)`. -/
  go (lo hi : Nat) : Option Nat :=
    if h : lo < hi then
      let mid := lo + (hi - lo) / 2
      if hm : mid < a.size then
        let v := a[mid]
        if v == target then some mid
        else if v < target then go (mid + 1) hi
        else go lo mid
      else none
    else none
  termination_by hi - lo

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
      simp [hlo, mid, hmid, v, heq]
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
          simp [hlo, hN, hmidBound, hnotEq, hlt']
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
          simpa [Nat.add_comm] using Nat.lt_succ_of_le hchild'
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
          simp [hlo, hN, hmidBound, hnotEq, hnotlt']
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
          simpa [Nat.add_comm] using Nat.lt_succ_of_le hchild'
  | case4 lo hi hlo mid hnotmid =>
      rw [binarySearch.goCalls.eq_1]
      simp [hlo, mid, hnotmid]
      exact binarySearchCalls_pos (hi - lo)
  | case5 lo hi hnotlo =>
      rw [binarySearch.goCalls.eq_1]
      simp [hnotlo]
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

/-! Correctness

Plan: prove statements about `go` (the loop), by well-founded induction on `hi - lo`
(or via `binarySearch.go.induct`), then specialize to `lo = 0`, `hi = a.size`.
-/

/-- Soundness of `go`: any returned index holds `target`. No sortedness needed. -/
theorem go_sound (a : Array Nat) (t : Nat) :
    ∀ lo hi i, binarySearch.go a t lo hi = some i → a[i]? = some t := by
  intro lo hi
  induction lo, hi using binarySearch.go.induct a t with
  | case1 lo hi hlo mid hmid v heq =>
      intro i hret
      have hv : a[mid] = t := by
        dsimp [v] at heq
        exact beq_iff_eq.mp heq
      rw [binarySearch.go.eq_1] at hret
      simp [hlo, mid, hmid, v, heq] at hret
      subst i
      simp [mid, hmid, hv]
  | case2 lo hi hlo mid hmid v hne hlt ih =>
      intro i hret
      apply ih i
      rw [binarySearch.go.eq_1] at hret
      simpa [hlo, mid, hmid, v, hne, hlt] using hret
  | case3 lo hi hlo mid hmid v hne hnotlt ih =>
      intro i hret
      apply ih i
      rw [binarySearch.go.eq_1] at hret
      simpa [hlo, mid, hmid, v, hne, hnotlt] using hret
  | case4 lo hi hlo mid hnotmid =>
      intro i hret
      rw [binarySearch.go.eq_1] at hret
      simp [hlo, mid, hnotmid] at hret
  | case5 lo hi hnotlo =>
      intro i hret
      rw [binarySearch.go.eq_1] at hret
      simp [hnotlo] at hret

/-- Completeness invariant: if `t` lies in the range `[lo, hi)` (at some index `k`),
and `a` is sorted, then `go lo hi` finds something. -/
theorem go_complete (a : Array Nat) (t : Nat) (hs : Sorted a) :
    ∀ lo hi k, lo ≤ k → k < hi → hi ≤ a.size → a[k]? = some t →
      (binarySearch.go a t lo hi).isSome := by
  intro lo hi
  induction lo, hi using binarySearch.go.induct a t with
  | case1 lo hi hlo mid hmid v heq =>
      intro k hlow hkh hsize hval
      rw [binarySearch.go.eq_1]
      simp [hlo, mid, hmid, v, heq]
  | case2 lo hi hlo mid hmid v hne hlt ih =>
      intro k hlow hkh hsize hval
      have hksize : k < a.size := Nat.lt_of_lt_of_le hkh hsize
      have hval' : a[k] = t := by
        simpa [hksize] using hval
      have hmk : mid < k := by
        by_contra hnot
        have hkm : k ≤ mid := Nat.le_of_not_gt hnot
        have hle : a[k] ≤ a[mid] := hs k mid hksize hmid hkm
        dsimp [v] at hlt
        omega
      rw [binarySearch.go.eq_1]
      simpa [hlo, mid, hmid, v, hne, hlt] using
        (ih k (Nat.succ_le_of_lt hmk) hkh hsize hval)
  | case3 lo hi hlo mid hmid v hne hnotlt ih =>
      intro k hlow hkh hsize hval
      have hksize : k < a.size := Nat.lt_of_lt_of_le hkh hsize
      have hval' : a[k] = t := by
        simpa [hksize] using hval
      have htv : t < v := by
        dsimp [v] at hne hnotlt
        simp [beq_iff_eq] at hne
        omega
      have hkm : k < mid := by
        by_contra hnot
        have hmk : mid ≤ k := Nat.le_of_not_gt hnot
        have hle : a[mid] ≤ a[k] := hs mid k hmid hksize hmk
        dsimp [v] at htv
        omega
      rw [binarySearch.go.eq_1]
      simpa [hlo, mid, hmid, v, hne, hnotlt] using
        (ih k hlow hkm (Nat.le_of_lt hmid) hval)
  | case4 lo hi hlo mid hnotmid =>
      intro k hlow hkh hsize hval
      dsimp [mid] at hnotmid
      omega
  | case5 lo hi hnotlo =>
      intro k hlow hkh hsize hval
      omega

theorem binarySearch_sound (a : Array Nat) (t i : Nat) :
    binarySearch a t = some i → a[i]? = some t :=
  go_sound a t 0 a.size i

theorem binarySearch_complete (a : Array Nat) (t : Nat) (hs : Sorted a) (h : t ∈ a) :
    (binarySearch a t).isSome := by
  obtain ⟨k, hk, rfl⟩ := Array.getElem_of_mem h
  exact go_complete a _ hs 0 a.size k (Nat.zero_le _) hk (Nat.le_refl _) (by simp [hk])
