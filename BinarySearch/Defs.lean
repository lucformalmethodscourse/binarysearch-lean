module

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
