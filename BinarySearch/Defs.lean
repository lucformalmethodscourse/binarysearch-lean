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
    -- Is the interval non-empty? `h` is kept as a proof for termination checking.
    if h : lo < hi then
      -- Midpoint; `lo + (hi - lo) / 2` avoids overflow in fixed-width languages.
      let mid := lo + (hi - lo) / 2
      -- Prove `mid` is in bounds so `a[mid]` needs no runtime check.
      if hm : mid < a.size then
        -- Probe the middle element.
        let v := a[mid]
        -- Found: return its index.
        if v == target then some mid
        -- Too small (array is sorted): target is right of `mid`; drop `mid` and everything left.
        else if v < target then go (mid + 1) hi
        -- Too big: target is left of `mid`; `hi` is exclusive, so `mid` is dropped too.
        else go lo mid
      -- `mid` out of bounds (only if `hi > a.size`): return `none` to stay total.
      else none
    -- Empty interval: target is absent.
    else none
  -- `hi - lo` strictly shrinks on every recursive call, so recursion terminates.
  termination_by hi - lo
