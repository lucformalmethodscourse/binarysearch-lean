module

import Mathlib.Tactic.Order
public import BinarySearch.Defs
public import Sorted

/-! Correctness proofs for binary search. -/

@[expose] public section

/-! Correctness

Both proofs reason about one call to `go`, whose search interval is `[lo, hi)`.
The induction follows the branches of the program: a midpoint match, a recursive
call into one half, or a stopping case. The public theorems then specialize the
interval to the whole array.
-/

/-- Soundness of `go`: any returned index holds `target`. No sortedness needed. -/
theorem go_sound (a : Array Nat) (t : Nat) :
    ∀ lo hi i, binarySearch.go a t lo hi = some i → a[i]? = some t := by
  intro lo hi
  induction lo, hi using binarySearch.go.induct a t with
  -- A match at the midpoint is the only way this call returns an index directly.
  | case1 lo hi hlo mid hmid v heq =>
      intro i hret
      have hv : a[mid] = t := by
        dsimp [v] at heq
        exact beq_iff_eq.mp heq
      rw [binarySearch.go.eq_1] at hret
      simp [hlo, mid, hmid, v, heq] at hret
      subst i
      simp [mid, hmid, hv]
  -- If the algorithm recurses, any returned index comes from that recursive call.
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
  -- Empty intervals and invalid midpoints return `none`, so cannot satisfy
  -- the hypothesis that this call returned `some i`.
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
  -- At a midpoint match, the search succeeds immediately.
  | case1 lo hi hlo mid hmid v heq =>
      intro k hlow hkh hsize hval
      rw [binarySearch.go.eq_1]
      simp [hlo, mid, hmid, v, heq]
  -- If the midpoint value is below t, sortedness rules out every target at or
  -- to the left of the midpoint, so the witness k must be in the right half.
  | case2 lo hi hlo mid hmid v hne hlt ih =>
      intro k hlow hkh hsize hval
      have hksize : k < a.size := Nat.lt_of_lt_of_le hkh hsize
      have hval' : a[k] = t := by
        simpa [hksize] using hval
      -- If k were at or left of mid, sortedness would give a[k] ≤ a[mid] < t,
      -- contradicting that a[k] = t.
      have hmk : mid < k := by
        by_contra hnot
        have hkm : k ≤ mid := Nat.le_of_not_gt hnot
        have hle : a[k] ≤ a[mid] := hs k mid hksize hmid hkm
        dsimp [v] at hlt
        omega
      rw [binarySearch.go.eq_1]
      simpa [hlo, mid, hmid, v, hne, hlt] using
        (ih k (Nat.succ_le_of_lt hmk) hkh hsize hval)
  -- Otherwise, the midpoint is above t; sortedness rules out the right half.
  | case3 lo hi hlo mid hmid v hne hnotlt ih =>
      intro k hlow hkh hsize hval
      have hksize : k < a.size := Nat.lt_of_lt_of_le hkh hsize
      have hval' : a[k] = t := by
        simpa [hksize] using hval
      have htv : t < v := by
        dsimp [v] at hne hnotlt
        simp [beq_iff_eq] at hne
        omega
      -- If k were at or right of mid, sortedness would give v = a[mid] ≤ a[k] = t.
      have hkm : k < mid := by
        by_contra hnot
        have hmk : mid ≤ k := Nat.le_of_not_gt hnot
        have hle : a[mid] ≤ a[k] := hs mid k hmid hksize hmk
        dsimp [v] at htv
        omega
      rw [binarySearch.go.eq_1]
      simpa [hlo, mid, hmid, v, hne, hnotlt] using
        (ih k hlow hkm (Nat.le_of_lt hmid) hval)
  -- The invariant's range hypotheses cannot hold when there is no valid
  -- midpoint or when the interval is empty.
  | case4 lo hi hlo mid hnotmid =>
      intro k hlow hkh hsize hval
      dsimp [mid] at hnotmid
      omega
  | case5 lo hi hnotlo =>
      intro k hlow hkh hsize hval
      omega

/-- Specialize `go_sound` to the initial whole-array interval. -/
theorem binarySearch_sound (a : Array Nat) (t i : Nat) :
    binarySearch a t = some i → a[i]? = some t :=
  go_sound a t 0 a.size i

/-- Turn membership in the array into an index witness, then use `go_complete`. -/
theorem binarySearch_complete (a : Array Nat) (t : Nat) (hs : Sorted a) (h : t ∈ a) :
    (binarySearch a t).isSome := by
  obtain ⟨k, hk, rfl⟩ := Array.getElem_of_mem h
  exact go_complete a _ hs 0 a.size k (Nat.zero_le _) hk (Nat.le_refl _) (by simp [hk])
