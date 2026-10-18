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

example : binarySearch #[1, 3, 5, 7, 9, 11] 7 = some 3 := by native_decide
example : binarySearch #[1, 3, 5, 7, 9, 11] 4 = none := by native_decide

/-! Correctness

Plan: prove statements about `go` (the loop), by well-founded induction on `hi - lo`
(or via `binarySearch.go.induct`), then specialize to `lo = 0`, `hi = a.size`.
-/

/-- Soundness of `go`: any returned index holds `target`. No sortedness needed. -/
theorem go_sound (a : Array Nat) (t : Nat) :
    ∀ lo hi i, binarySearch.go a t lo hi = some i → a[i]? = some t := by
  intro lo hi
  induction lo, hi using binarySearch.go.induct a t with
  | _ => sorry -- unfold `binarySearch.go`, split on the ifs, use IH / `simp_all`

/-- Completeness invariant: if `t` lies in the range `[lo, hi)` (at some index `k`),
and `a` is sorted, then `go lo hi` finds something. -/
theorem go_complete (a : Array Nat) (t : Nat) (hs : Sorted a) :
    ∀ lo hi k, lo ≤ k → k < hi → hi ≤ a.size → a[k]? = some t →
      (binarySearch.go a t lo hi).isSome := by
  intro lo hi
  induction lo, hi using binarySearch.go.induct a t with
  | _ => sorry -- case v < t: k ≥ mid+1 by sortedness (hs); case v > t: k < mid; use IH

theorem binarySearch_sound (a : Array Nat) (t i : Nat) :
    binarySearch a t = some i → a[i]? = some t :=
  go_sound a t 0 a.size i

theorem binarySearch_complete (a : Array Nat) (t : Nat) (hs : Sorted a) (h : t ∈ a) :
    (binarySearch a t).isSome := by
  obtain ⟨k, hk, rfl⟩ := Array.getElem_of_mem h
  exact go_complete a _ hs 0 a.size k (Nat.zero_le _) hk (Nat.le_refl _) (by simp [hk])
