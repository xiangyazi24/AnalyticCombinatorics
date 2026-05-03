/-
  Analytic Combinatorics — Part A: Symbolic Method
  Chapter I: Lagrange-Bürmann Inversion — numerical verifications.

  Numerical verifications of Lagrange-Bürmann inversion and functional
  equation solutions (Flajolet & Sedgewick, Ch I/II).
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticInversion

/-! ## 1. Lagrange Inversion for Catalan (Binary Trees)

  T(z) = z·(1+T(z))² encodes binary trees by size.
  By Lagrange: [z^n]T = (1/n)·C(2n, n-1) = C(2n,n)/(n+1) = Catalan(n).

  Numerical identity: C(2n, n-1)/n = C(2n, n)/(n+1) for n ≥ 1.
-/

/-- Catalan number via Lagrange: C(2n,n)/(n+1). -/
def catalanLagrange (n : ℕ) : ℕ := Nat.choose (2 * n) n / (n + 1)

theorem catalanLagrange_0 : catalanLagrange 0 = 1 := by native_decide
theorem catalanLagrange_1 : catalanLagrange 1 = 1 := by native_decide
theorem catalanLagrange_2 : catalanLagrange 2 = 2 := by native_decide
theorem catalanLagrange_3 : catalanLagrange 3 = 5 := by native_decide
theorem catalanLagrange_4 : catalanLagrange 4 = 14 := by native_decide
theorem catalanLagrange_5 : catalanLagrange 5 = 42 := by native_decide
theorem catalanLagrange_6 : catalanLagrange 6 = 132 := by native_decide

/-- Lagrange formula cross-check: C(2n, n-1)/n = C(2n, n)/(n+1) for small n.
    The left side is the Lagrange extraction (1/n)·[w^{n-1}](1+w)^{2n};
    the right side is the standard Catalan formula. -/
example : Nat.choose 6 2 / 3 = Nat.choose 6 3 / 4 := by native_decide   -- n=3: 5 = 5
example : Nat.choose 8 3 / 4 = Nat.choose 8 4 / 5 := by native_decide   -- n=4: 14 = 14
example : Nat.choose 10 4 / 5 = Nat.choose 10 5 / 6 := by native_decide  -- n=5: 42 = 42
example : Nat.choose 12 5 / 6 = Nat.choose 12 6 / 7 := by native_decide  -- n=6: 132 = 132

/-! ## 2. Lagrange Inversion for General Trees (T = z/(1-T))

  T(z) = z/(1-T(z)) encodes plane trees (all ordered trees) by size.
  Equivalently T - T² = z, giving T = (1-√(1-4z))/2.
  By Lagrange: [z^n]T = C(2n-2, n-1)/n for n ≥ 1.
  These are the Catalan numbers shifted by one: [z^n]T = Catalan(n-1).
-/

/-- [z^n]T for T = z/(1-T): equals C(2n-2,n-1)/n = Catalan(n-1) for n ≥ 1. -/
def planTreeCoeff : ℕ → ℕ
  | 0 => 0   -- coefficient of z^0 is 0
  | n + 1 => Nat.choose (2 * n) n / (n + 1)

theorem planTreeCoeff_1 : planTreeCoeff 1 = 1 := by native_decide   -- C(0,0)/1 = 1
theorem planTreeCoeff_2 : planTreeCoeff 2 = 1 := by native_decide   -- C(2,1)/2 = 1
theorem planTreeCoeff_3 : planTreeCoeff 3 = 2 := by native_decide   -- C(4,2)/3 = 2
theorem planTreeCoeff_4 : planTreeCoeff 4 = 5 := by native_decide   -- C(6,3)/4 = 5
theorem planTreeCoeff_5 : planTreeCoeff 5 = 14 := by native_decide  -- C(8,4)/5 = 14
theorem planTreeCoeff_6 : planTreeCoeff 6 = 42 := by native_decide  -- C(10,5)/6 = 42

-- Direct verification of the formula values
example : Nat.choose 0 0 / 1 = 1 := by native_decide
example : Nat.choose 2 1 / 2 = 1 := by native_decide
example : Nat.choose 4 2 / 3 = 2 := by native_decide
example : Nat.choose 6 3 / 4 = 5 := by native_decide
example : Nat.choose 8 4 / 5 = 14 := by native_decide

/-! ## 3. Lagrange Inversion for Labelled Rooted Trees (Lambert W / Cayley)

  T(z) = z·e^{T(z)} has the exponential generating function for rooted
  labelled trees (Cayley's formula).  [z^n/n!]T = n^{n-1} for n ≥ 1,
  so the number of rooted labelled trees on n vertices is n^{n-1}.
-/

/-- Number of rooted labelled trees on n vertices: n^{n-1} (Cayley). -/
def rootedLabelled (n : ℕ) : ℕ := if n = 0 then 0 else n ^ (n - 1)

theorem rootedLabelled_1 : rootedLabelled 1 = 1 := by native_decide
theorem rootedLabelled_2 : rootedLabelled 2 = 2 := by native_decide
theorem rootedLabelled_3 : rootedLabelled 3 = 9 := by native_decide
theorem rootedLabelled_4 : rootedLabelled 4 = 64 := by native_decide
theorem rootedLabelled_5 : rootedLabelled 5 = 625 := by native_decide
theorem rootedLabelled_6 : rootedLabelled 6 = 7776 := by native_decide

/-- For n ≥ 2, rootedLabelled n = n * n^{n-2} (unrooting the root). -/
theorem rootedLabelled_factor (n : ℕ) (hn : 2 ≤ n) :
    rootedLabelled n = n * n ^ (n - 2) := by
  have hn0 : n ≠ 0 := by omega
  simp only [rootedLabelled, hn0, if_false]
  cases n with
  | zero => omega
  | succ m =>
    cases m with
    | zero => omega
    | succ k =>
      simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
      ring

/-! ## 4. Bürmann Formula: [z^n](1/(1-T)) for T = z·(1+T)

  When T(z) = z/(1-z) (geometric case, φ(w)=1+w after shifting), we get
  [z^n](1/(1-T)) = C(2n, n), the central binomial coefficients.
  This follows from the Bürmann series extension of Lagrange inversion.
-/

/-- Central binomial coefficient C(2n, n). -/
def centralBinomial (n : ℕ) : ℕ := Nat.choose (2 * n) n

theorem centralBinomial_0 : centralBinomial 0 = 1 := by native_decide
theorem centralBinomial_1 : centralBinomial 1 = 2 := by native_decide
theorem centralBinomial_2 : centralBinomial 2 = 6 := by native_decide
theorem centralBinomial_3 : centralBinomial 3 = 20 := by native_decide
theorem centralBinomial_4 : centralBinomial 4 = 70 := by native_decide
theorem centralBinomial_5 : centralBinomial 5 = 252 := by native_decide
theorem centralBinomial_6 : centralBinomial 6 = 924 := by native_decide

-- Direct formula checks
example : Nat.choose 0 0 = 1 := by native_decide
example : Nat.choose 2 1 = 2 := by native_decide
example : Nat.choose 4 2 = 6 := by native_decide
example : Nat.choose 6 3 = 20 := by native_decide
example : Nat.choose 8 4 = 70 := by native_decide
example : Nat.choose 10 5 = 252 := by native_decide

/-! ## 5. Implicit Function / Quadratic Method: Divisibility for Catalan

  The functional equation y = z·(1+y)² gives Catalan numbers as coefficients.
  The quadratic method yields y = (1-2z-√(1-4z))/(2z).
  A key identity: (n+1) | C(2n, n), which is needed to make the formula integral.
-/

/-- (n+1) divides the central binomial C(2n, n) (needed for Catalan integrality). -/
theorem catalan_divisibility_4 : Nat.choose 8 4 % 5 = 0 := by native_decide
theorem catalan_divisibility_5 : Nat.choose 10 5 % 6 = 0 := by native_decide
theorem catalan_divisibility_6 : Nat.choose 12 6 % 7 = 0 := by native_decide
theorem catalan_divisibility_7 : Nat.choose 14 7 % 8 = 0 := by native_decide
theorem catalan_divisibility_8 : Nat.choose 16 8 % 9 = 0 := by native_decide
theorem catalan_divisibility_9 : Nat.choose 18 9 % 10 = 0 := by native_decide

/-- The Catalan number C_n = C(2n,n)/(n+1) is a natural number for n ≤ 10.
    Checked individually via native_decide. -/
theorem catalan_integral_0 : (0 + 1) ∣ Nat.choose (2 * 0) 0 := by native_decide
theorem catalan_integral_1 : (1 + 1) ∣ Nat.choose (2 * 1) 1 := by native_decide
theorem catalan_integral_2 : (2 + 1) ∣ Nat.choose (2 * 2) 2 := by native_decide
theorem catalan_integral_3 : (3 + 1) ∣ Nat.choose (2 * 3) 3 := by native_decide
theorem catalan_integral_4 : (4 + 1) ∣ Nat.choose (2 * 4) 4 := by native_decide
theorem catalan_integral_5 : (5 + 1) ∣ Nat.choose (2 * 5) 5 := by native_decide
theorem catalan_integral_6 : (6 + 1) ∣ Nat.choose (2 * 6) 6 := by native_decide
theorem catalan_integral_7 : (7 + 1) ∣ Nat.choose (2 * 7) 7 := by native_decide
theorem catalan_integral_8 : (8 + 1) ∣ Nat.choose (2 * 8) 8 := by native_decide
theorem catalan_integral_9 : (9 + 1) ∣ Nat.choose (2 * 9) 9 := by native_decide
theorem catalan_integral_10 : (10 + 1) ∣ Nat.choose (2 * 10) 10 := by native_decide

/-! ## 6. Motzkin Recurrence via Functional Equation

  The Motzkin GF M(z) satisfies M = 1 + z·M + z²·M².
  This gives the recurrence for Motzkin numbers:
    M_0 = 1, M_1 = 1,
    M_{n+2} = M_{n+1} + Σ_{k=0}^{n} M_k · M_{n-k}.
-/

/-- Motzkin numbers via the functional equation M = 1 + z·M + z²·M².
    The recurrence M_{n+2} = M_{n+1} + Σ_{k=0}^{n} M_k * M_{n-k} comes from
    extracting z^{n+2} coefficients of M = 1 + z*M + z^2*M^2. -/
def motzkinLagrange : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | (n + 2) =>
      motzkinLagrange (n + 1) +
      ∑ i : (Finset.range (n + 1) : Set ℕ),
        motzkinLagrange i.1 * motzkinLagrange (n - i.1)
  termination_by n => n
  decreasing_by
    all_goals simp_wf
    all_goals
      try
        have hi := Finset.mem_range.mp (show i.1 ∈ Finset.range (n + 1) from i.2)
      omega

theorem motzkinLagrange_0 : motzkinLagrange 0 = 1 := by native_decide
theorem motzkinLagrange_1 : motzkinLagrange 1 = 1 := by native_decide
theorem motzkinLagrange_2 : motzkinLagrange 2 = 2 := by native_decide
theorem motzkinLagrange_3 : motzkinLagrange 3 = 4 := by native_decide
theorem motzkinLagrange_4 : motzkinLagrange 4 = 9 := by native_decide
theorem motzkinLagrange_5 : motzkinLagrange 5 = 21 := by native_decide
theorem motzkinLagrange_6 : motzkinLagrange 6 = 51 := by native_decide
theorem motzkinLagrange_7 : motzkinLagrange 7 = 127 := by native_decide

/-- The Motzkin recurrence matches the standard sequence for n ≤ 7. -/
theorem motzkinLagrange_seq :
    (List.map motzkinLagrange (List.range 8)) =
    [1, 1, 2, 4, 9, 21, 51, 127] := by native_decide

/-! ## Summary table: Catalan, plane-tree, rooted-labelled, central-binomial -/

/-- Consistency: catalanLagrange n = planTreeCoeff (n+1) for n = 0..7. -/
theorem catalan_eq_planTree_0 : catalanLagrange 0 = planTreeCoeff 1 := by native_decide
theorem catalan_eq_planTree_1 : catalanLagrange 1 = planTreeCoeff 2 := by native_decide
theorem catalan_eq_planTree_2 : catalanLagrange 2 = planTreeCoeff 3 := by native_decide
theorem catalan_eq_planTree_3 : catalanLagrange 3 = planTreeCoeff 4 := by native_decide
theorem catalan_eq_planTree_4 : catalanLagrange 4 = planTreeCoeff 5 := by native_decide
theorem catalan_eq_planTree_5 : catalanLagrange 5 = planTreeCoeff 6 := by native_decide
theorem catalan_eq_planTree_6 : catalanLagrange 6 = planTreeCoeff 7 := by native_decide

/-- Consistency: centralBinomial recurrence check at n=5.
    C(10,5) = C(8,4) * 9 / 5 * 2 is the standard recurrence C(2n,n) = 2*(2n-1)/n * C(2(n-1),n-1). -/
example : centralBinomial 5 = centralBinomial 4 * 9 / 5 * 2 := by native_decide

end AnalyticInversion
