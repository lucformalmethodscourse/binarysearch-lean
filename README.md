# binarysearch-lean

An executable binary search on `Array Nat`, developed in Lean 4 with
machine-checked correctness proofs and a formal analysis of its recursive-call
complexity. The project explores how programming, specifications, proofs, and
algorithm analysis can fit together in an introductory computer science course.

## Project layout

| File | Purpose |
|------|---------|
| [BinarySearch.lean](./BinarySearch.lean) | Public umbrella module for the binary-search API |
| [BinarySearch/Defs.lean](./BinarySearch/Defs.lean) | Search implementation on a half-open interval |
| [BinarySearch/Examples.lean](./BinarySearch/Examples.lean) | Evaluations and concrete example proofs |
| [BinarySearch/Correctness.lean](./BinarySearch/Correctness.lean) | Soundness and completeness theorems |
| [BinarySearch/Complexity.lean](./BinarySearch/Complexity.lean) | Recursive-call recurrence and logarithmic bounds |
| [Sorted.lean](./Sorted.lean) | Reusable sortedness predicate and concrete examples |
| [SquareOfEven.lean](./SquareOfEven.lean) | Small standalone proof example |
| [doc/ai/](./doc/ai) | Timestamped transcripts of AI-assisted sessions |

`BinarySearch.lean` re-exports the definitions, correctness theorems, and
complexity results. `Sorted` remains a separate root module so it can be reused
independently of binary search.

## Specification and correctness

`binarySearch a t : Option Nat` returns an index containing `t`, or `none`.
The implementation does not check whether `a` is sorted. Instead, sortedness is
a precondition of the completeness theorem:

- `binarySearch_sound`: any returned index `i` satisfies `a[i]? = some t`;
  sortedness is not needed.
- `binarySearch_complete`: if `a` is sorted and contains `t`, the result is
  `some` index.

This separates what the program computes from the assumptions needed to prove
its guarantees.

## Complexity model

The complexity module defines a worst-case recurrence for the number of
recursive calls and proves that the implementation's call count is bounded by a
logarithmic function of the array size. In particular,
`binarySearchCalls_isBigO` states the asymptotic bound.

This is a proof about recursive calls, not directly about elapsed time or space.
Interpreting it as time complexity assumes the operations performed in each
call—such as array indexing and comparisons—take constant time.

## Pedagogical use

The algorithm and its informal analysis fit naturally with data structures and
algorithms. The full Lean development is especially useful for studying
preconditions, precise correctness claims, and what a formal cost model does
and does not establish.

## Build

Requires [Lean 4 via elan](https://lean-lang.org/install/); the toolchain and
Mathlib versions are pinned in the project configuration.

```sh
lake exe cache get   # optional: fetch prebuilt Mathlib
lake build
```
