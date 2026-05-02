# Task: Motzkin Trees (v2, simplified)

## Goal

Create `AnalyticCombinatorics/PartA/Ch1/MotzkinTrees.lean`.

## Approach

Use the SIMPLEST possible finite_level proof. Do NOT build an explicit `ofSize` Finset. Instead:

```lean
inductive MotzkinTree where
  | leaf : MotzkinTree
  | unary : MotzkinTree → MotzkinTree
  | binary : MotzkinTree → MotzkinTree → MotzkinTree

def MotzkinTree.size : MotzkinTree → ℕ
  | .leaf => 1
  | .unary t => 1 + t.size
  | .binary l r => 1 + l.size + r.size
```

For `finite_level`, use the same strategy as Trees.lean in this repo: define a list enumerator using well-founded recursion and prove it covers all elements. Look at how `AnalyticCombinatorics/PartA/Ch1/Trees.lean` does `BinaryTree.finite_level` — copy that pattern exactly.

## Required theorems

1. `motzkinTreeClass : CombinatorialClass`
2. Sanity checks via native_decide:
   - count 1 = 1
   - count 2 = 1
   - count 3 = 2
   - count 4 = 4
   - count 5 = 9

3. OGF equation: `motzkinTreeClass.ogf = X * (1 + motzkinTreeClass.ogf + motzkinTreeClass.ogf ^ 2)`

## Key constraint

**The file MUST compile with `lake build AnalyticCombinatorics.PartA.Ch1.MotzkinTrees` before you write the reply.** If any theorem doesn't compile, delete it rather than leaving it broken.

No sorry, no axiom.

## Output

Write file, verify build, report.
