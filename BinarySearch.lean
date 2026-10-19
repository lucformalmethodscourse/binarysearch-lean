import Sorted

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
