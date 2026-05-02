Done.

Created `AnalyticCombinatorics/PartA/Ch1/Trees.lean`.

Proved:
- `BinaryTree` with `leaf` and `node`.
- `BinaryTree.size`, with leaves size `0` and nodes size `1 + size l + size r`.
- finite level construction `BinaryTree.ofSize` and theorem `BinaryTree.mem_ofSize_iff`.
- `binaryTreeClass : CombinatorialClass`.
- `binaryTree_count_recursion`.
- `binaryTree_ogf_eq : binaryTreeClass.ogf = 1 + X * binaryTreeClass.ogf ^ 2`.
- sanity counts `0..4`: `1, 1, 2, 5, 14`.
- initial central-binomial/Catalan checks for `0..4`.

Verification:
- `lake build AnalyticCombinatorics.PartA.Ch1.Trees` passes.

Notes:
- Focused on binary trees only, as requested.
- Existing unrelated worktree changes were left untouched.
