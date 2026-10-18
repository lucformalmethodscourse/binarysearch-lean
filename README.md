# binarysearch-lean

Binary search on sorted `Array Nat` in Lean 4, with a specification and correctness theorems.
A CS 335 teaching project.

## Contents

| File | Purpose |
|------|---------|
| [BinarySearch.lean](./BinarySearch.lean) | `binarySearch`, example evaluations, soundness/completeness theorem skeletons |
| [Sorted.lean](./Sorted.lean) | `Sorted` predicate, example evaluations, and proof macros (`sorted_by_cases`, `not_sorted_at`) |
| [SquareOfEven.lean](./SquareOfEven.lean) | Small standalone proof example |
| [doc/ai/](./doc/ai) | Timestamped transcripts of AI-assisted sessions |

## Design

- `binarySearch a t : Option Nat` returns an index holding `t`, or `none`.
- Sortedness is a theorem precondition, not checked at runtime, so the search stays O(log n).
- Specs: `binarySearch_sound` (a result `i` satisfies `a[i]? = some t`) and
  `binarySearch_complete` (`Sorted a → t ∈ a → (binarySearch a t).isSome`).

## Status

`go_sound` and `go_complete` are still `sorry`. The return type (`Option` vs. insertion point)
is under discussion.

## Build

Requires [Lean 4 via elan](https://lean-lang.org/install/); the toolchain and Mathlib versions are pinned.

```sh
lake exe cache get   # optional: fetch prebuilt Mathlib
lake build BinarySearch
```
