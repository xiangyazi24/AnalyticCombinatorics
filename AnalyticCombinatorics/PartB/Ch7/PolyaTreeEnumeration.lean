import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace PolyaTreeEnumeration

/-!
  Polya-type finite checks for unlabelled tree enumeration.

  The tables record the initial coefficients used in Chapter VII:
  rooted unlabelled trees, free unlabelled trees, Wedderburn-Etherington
  binary trees, and Catalan plane trees.
-/

/-! ## Rooted unlabelled trees: OEIS A000081 -/

/-- Initial values of rooted unlabelled trees, indexed by `n = 0, ..., 9`. -/
def rootedTreeTable : Fin 10 → ℕ :=
  ![0, 1, 1, 2, 4, 9, 20, 48, 115, 286]

/-- Rooted unlabelled tree count `t(n)` on the tabulated range. -/
def rootedTree (n : ℕ) : ℕ :=
  if h : n < 10 then rootedTreeTable ⟨n, h⟩ else 0

theorem rootedTree_values :
    [rootedTree 0, rootedTree 1, rootedTree 2, rootedTree 3, rootedTree 4,
      rootedTree 5, rootedTree 6, rootedTree 7, rootedTree 8, rootedTree 9] =
    [0, 1, 1, 2, 4, 9, 20, 48, 115, 286] := by
  native_decide

theorem rootedTree_fin_table :
    ∀ i : Fin 10, rootedTree i.val = rootedTreeTable i := by
  native_decide

/-! ## Polya recurrence for rooted unlabelled trees -/

/-- Divisor sum appearing in the coefficient recurrence from
`T(z) = z exp(sum_{k ≥ 1} T(z^k) / k)`. -/
def polyaDivisorSum (k : ℕ) : ℕ :=
  (Finset.Icc 1 k).sum (fun d => if d ∣ k then d * rootedTree d else 0)

/-- Right hand side of `(n - 1) t(n) = sum_{k=1}^{n-1} b_k t(n-k)`. -/
def rootedPolyaRhs (n : ℕ) : ℕ :=
  (Finset.Icc 1 (n - 1)).sum (fun k => polyaDivisorSum k * rootedTree (n - k))

theorem rooted_polya_recurrence_2_9 :
    ∀ i : Fin 8,
      let n := i.val + 2
      (n - 1) * rootedTree n = rootedPolyaRhs n := by
  native_decide

/-! ## Free unlabelled trees: OEIS A000055 -/

/-- Initial values of unrooted unlabelled trees, indexed by `n = 0, ..., 9`.
The first entry is the conventional empty-size placeholder for this file. -/
def unrootedTreeTable : Fin 10 → ℕ :=
  ![1, 1, 1, 1, 2, 3, 6, 11, 23, 47]

/-- Unrooted unlabelled tree count on the tabulated range. -/
def unrootedTree (n : ℕ) : ℕ :=
  if h : n < 10 then unrootedTreeTable ⟨n, h⟩ else 0

theorem unrootedTree_values :
    [unrootedTree 0, unrootedTree 1, unrootedTree 2, unrootedTree 3, unrootedTree 4,
      unrootedTree 5, unrootedTree 6, unrootedTree 7, unrootedTree 8, unrootedTree 9] =
    [1, 1, 1, 1, 2, 3, 6, 11, 23, 47] := by
  native_decide

theorem unrootedTree_fin_table :
    ∀ i : Fin 10, unrootedTree i.val = unrootedTreeTable i := by
  native_decide

/-! ## Otter dissimilarity formula -/

/-- Coefficient of `T(z)^2` in degree `n`. -/
def rootedPairProduct (n : ℕ) : ℕ :=
  (Finset.Icc 1 (n - 1)).sum (fun k => rootedTree k * rootedTree (n - k))

/-- Coefficient of `T(z^2)` in degree `n`. -/
def rootedDiagonalCorrection (n : ℕ) : ℕ :=
  if n % 2 = 0 then rootedTree (n / 2) else 0

/-- Otter's unordered-pair correction:
`( [z^n] T(z)^2 - [z^n] T(z^2) ) / 2`. -/
def rootedChooseTwoCorrection (n : ℕ) : ℕ :=
  (rootedPairProduct n - rootedDiagonalCorrection n) / 2

/-- Otter formula right hand side: `T_n - (T^2 - T(z^2))_n / 2`. -/
def otterRhs (n : ℕ) : ℕ :=
  rootedTree n - rootedChooseTwoCorrection n

theorem otter_correction_values_1_9 :
    [rootedChooseTwoCorrection 1, rootedChooseTwoCorrection 2,
      rootedChooseTwoCorrection 3, rootedChooseTwoCorrection 4,
      rootedChooseTwoCorrection 5, rootedChooseTwoCorrection 6,
      rootedChooseTwoCorrection 7, rootedChooseTwoCorrection 8,
      rootedChooseTwoCorrection 9] =
    [0, 0, 1, 2, 6, 14, 37, 92, 239] := by
  native_decide

theorem otter_formula_1_9 :
    ∀ i : Fin 9, unrootedTree (i.val + 1) = otterRhs (i.val + 1) := by
  native_decide

/-! ## Labelled versus unlabelled counts -/

/-- Cayley's labelled unrooted tree count `n^(n-2)`, with `n = 0, 1` set to `1`. -/
def labelledTreeCount (n : ℕ) : ℕ :=
  if n ≤ 1 then 1 else n ^ (n - 2)

/-- Number of label assignments to rooted unlabelled shapes in the finite table. -/
def labelledRootedShapeAssignments (n : ℕ) : ℕ :=
  Nat.factorial n * rootedTree n

/-- Row comparing `n! * t(n)` with Cayley's labelled count `n^(n-2)`. -/
def labelledVsUnlabelledRow (n : ℕ) : ℕ × ℕ :=
  (labelledRootedShapeAssignments n, labelledTreeCount n)

/-- Finite comparison table for `n = 1, ..., 9`. -/
def labelledVsUnlabelledTable : Fin 9 → ℕ × ℕ :=
  ![(1, 1), (2, 1), (12, 3), (96, 16), (1080, 125),
    (14400, 1296), (241920, 16807), (4636800, 262144),
    (103783680, 4782969)]

theorem labelled_vs_unlabelled_ratio_table :
    ∀ i : Fin 9,
      labelledVsUnlabelledRow (i.val + 1) = labelledVsUnlabelledTable i := by
  native_decide

theorem labelled_rooted_assignments_dominate_cayley_2_9 :
    ∀ i : Fin 8,
      labelledTreeCount (i.val + 2) ≤ labelledRootedShapeAssignments (i.val + 2) := by
  native_decide

/-! ## Wedderburn-Etherington binary trees: OEIS A001190 -/

/-- Initial values of unlabelled binary trees, indexed by `n = 0, ..., 9`. -/
def wedderburnEtheringtonTable : Fin 10 → ℕ :=
  ![0, 1, 1, 1, 2, 3, 6, 11, 23, 46]

/-- Wedderburn-Etherington count on the tabulated range. -/
def wedderburnEtherington (n : ℕ) : ℕ :=
  if h : n < 10 then wedderburnEtheringtonTable ⟨n, h⟩ else 0

theorem wedderburnEtherington_values :
    [wedderburnEtherington 0, wedderburnEtherington 1,
      wedderburnEtherington 2, wedderburnEtherington 3,
      wedderburnEtherington 4, wedderburnEtherington 5,
      wedderburnEtherington 6, wedderburnEtherington 7,
      wedderburnEtherington 8, wedderburnEtherington 9] =
    [0, 1, 1, 1, 2, 3, 6, 11, 23, 46] := by
  native_decide

theorem wedderburnEtherington_fin_table :
    ∀ i : Fin 10, wedderburnEtherington i.val = wedderburnEtheringtonTable i := by
  native_decide

/-! ## Plane trees versus non-plane rooted trees -/

/-- Plane rooted trees counted by Catalan numbers. -/
def catalanNumber (n : ℕ) : ℕ :=
  Nat.choose (2 * n) n / (n + 1)

/-- Row comparing Catalan plane trees with rooted non-plane trees. -/
def planeVsNonplaneRow (n : ℕ) : ℕ × ℕ :=
  (catalanNumber n, rootedTree n)

/-- Finite comparison table for `n = 0, ..., 9`. -/
def planeVsNonplaneTable : Fin 10 → ℕ × ℕ :=
  ![(1, 0), (1, 1), (2, 1), (5, 2), (14, 4),
    (42, 9), (132, 20), (429, 48), (1430, 115), (4862, 286)]

theorem plane_vs_nonplane_table :
    ∀ i : Fin 10, planeVsNonplaneRow i.val = planeVsNonplaneTable i := by
  native_decide

/-- Integer quotient `Catalan(n) / t(n)` on the nonzero tabulated range. -/
def planeNonplaneQuotient (n : ℕ) : ℕ :=
  catalanNumber n / rootedTree n

theorem plane_nonplane_quotient_values_1_9 :
    [planeNonplaneQuotient 1, planeNonplaneQuotient 2,
      planeNonplaneQuotient 3, planeNonplaneQuotient 4,
      planeNonplaneQuotient 5, planeNonplaneQuotient 6,
      planeNonplaneQuotient 7, planeNonplaneQuotient 8,
      planeNonplaneQuotient 9] =
    [1, 2, 2, 3, 4, 6, 8, 12, 17] := by
  native_decide

/-- Finite factorial-scale lower check for the plane/non-plane ratio. -/
theorem plane_nonplane_factorial_scale_1_9 :
    ∀ i : Fin 9,
      Nat.factorial ((i.val + 1) / 3) * rootedTree (i.val + 1) ≤
        catalanNumber (i.val + 1) := by
  native_decide

end PolyaTreeEnumeration
