/-
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter IV — Tauberian Theorems and Convergence

  Numerical verifications related to:
  • Abel summation (partial summation / summation by parts)
  • Cesàro means and convergence
  • Dirichlet series partial sums
  • Fibonacci / Cassini's identity (radius of convergence)
  • Geometric series and GF coefficient extraction
  • Exponential generating function partial sums (e approximations)
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch4.TauberianTheorems
/-! ## 1. Geometric partial sums (Abel summation setup)

  Abel summation reduces Σ a_k b_k to telescoping.  A classical special case
  is the geometric series identity Σ_{k=0}^n r^k = r^{n+1} - 1 (for r ≠ 1).
  We verify specific instances in ℕ. -/

/-- Geometric partial sum: Σ_{k=0}^5 2^k = 63 = 2^6 - 1. -/
def geomPartialSum (r n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), r ^ k

example : geomPartialSum 2 5 = 63 := by native_decide
example : geomPartialSum 3 4 = 121 := by native_decide

-- Verify the formula: geomPartialSum r n = r^(n+1) - 1  (in ℕ, for r ≥ 2)
example : geomPartialSum 2 0  = 2 ^ 1  - 1 := by native_decide
example : geomPartialSum 2 1  = 2 ^ 2  - 1 := by native_decide
example : geomPartialSum 2 2  = 2 ^ 3  - 1 := by native_decide
example : geomPartialSum 2 3  = 2 ^ 4  - 1 := by native_decide
example : geomPartialSum 2 4  = 2 ^ 5  - 1 := by native_decide
example : geomPartialSum 2 5  = 2 ^ 6  - 1 := by native_decide
example : geomPartialSum 2 6  = 2 ^ 7  - 1 := by native_decide
example : geomPartialSum 2 7  = 2 ^ 8  - 1 := by native_decide
example : geomPartialSum 2 8  = 2 ^ 9  - 1 := by native_decide
example : geomPartialSum 2 9  = 2 ^ 10 - 1 := by native_decide
example : geomPartialSum 2 10 = 2 ^ 11 - 1 := by native_decide

-- Base 3: Σ_{k=0}^n 3^k = (3^{n+1} - 1) / 2
example : geomPartialSum 3 0 = (3 ^ 1 - 1) / 2 := by native_decide
example : geomPartialSum 3 1 = (3 ^ 2 - 1) / 2 := by native_decide
example : geomPartialSum 3 2 = (3 ^ 3 - 1) / 2 := by native_decide
example : geomPartialSum 3 3 = (3 ^ 4 - 1) / 2 := by native_decide
example : geomPartialSum 3 4 = (3 ^ 5 - 1) / 2 := by native_decide
example : geomPartialSum 3 7 = (3 ^ 8 - 1) / 2 := by native_decide

-- Directly as Finset.range sums (no definition wrapper)
example : ∑ k ∈ Finset.range 11, 2 ^ k = 2 ^ 11 - 1 := by native_decide
example : ∑ k ∈ Finset.range 8,  3 ^ k = (3 ^ 8 - 1) / 2 := by native_decide

/-! ## 2. Cesàro means

  For an alternating sequence s_n = (−1)^n the arithmetic means converge to 1/2
  even though the sequence itself diverges.  We compute rational exact values:

    cesaroAlt n = (Σ_{k=0}^n (−1)^k) / (n+1)

  Pattern:
    cesaroAlt (2*m)   = 1/(2*m+1)
    cesaroAlt (2*m+1) = 0                                                   -/

def cesaroAlt (n : ℕ) : ℚ :=
  (∑ k ∈ Finset.range (n + 1), ((-1 : ℚ) ^ k)) / ((n + 1 : ℚ))

-- Spot-check values
example : cesaroAlt 0 = 1       := by native_decide
example : cesaroAlt 1 = 0       := by native_decide
example : cesaroAlt 2 = 1 / 3   := by native_decide
example : cesaroAlt 3 = 0       := by native_decide
example : cesaroAlt 4 = 1 / 5   := by native_decide
example : cesaroAlt 5 = 0       := by native_decide
example : cesaroAlt 6 = 1 / 7   := by native_decide
example : cesaroAlt 7 = 0       := by native_decide
example : cesaroAlt 8 = 1 / 9   := by native_decide
example : cesaroAlt 9 = 0       := by native_decide
example : cesaroAlt 10 = 1 / 11 := by native_decide

-- General pattern for even indices: cesaroAlt (2*n) = 1/(2*n+1)
example : cesaroAlt (2 * 0) = 1 / (2 * 0 + 1) := by native_decide
example : cesaroAlt (2 * 1) = 1 / (2 * 1 + 1) := by native_decide
example : cesaroAlt (2 * 2) = 1 / (2 * 2 + 1) := by native_decide
example : cesaroAlt (2 * 3) = 1 / (2 * 3 + 1) := by native_decide
example : cesaroAlt (2 * 4) = 1 / (2 * 4 + 1) := by native_decide
example : cesaroAlt (2 * 5) = 1 / (2 * 5 + 1) := by native_decide

-- Odd indices are always 0
example : cesaroAlt (2 * 0 + 1) = 0 := by native_decide
example : cesaroAlt (2 * 1 + 1) = 0 := by native_decide
example : cesaroAlt (2 * 2 + 1) = 0 := by native_decide
example : cesaroAlt (2 * 3 + 1) = 0 := by native_decide
example : cesaroAlt (2 * 4 + 1) = 0 := by native_decide

/-! ## 3. Dirichlet series partial sums

  For the Riemann zeta function ζ(s) = Σ_{k=1}^∞ 1/k^s, the partial sums
  converge slowly.  We compute exact rational values for s = 2 and s = 3.

    dirichletPartial s n = Σ_{k=0}^{n-1} 1/(k+1)^s                         -/

def dirichletPartial (s n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, 1 / ((k + 1 : ℚ)) ^ s

-- ζ(2) partial sums: 1 + 1/4 + 1/9 + ...
example : dirichletPartial 2 1 = 1         := by native_decide
example : dirichletPartial 2 2 = 5 / 4     := by native_decide
example : dirichletPartial 2 3 = 49 / 36   := by native_decide
example : dirichletPartial 2 4 = 205 / 144 := by native_decide
example : dirichletPartial 2 5 = 5269 / 3600 := by native_decide

-- ζ(3) partial sums: 1 + 1/8 + 1/27 + ...
example : dirichletPartial 3 1 = 1           := by native_decide
example : dirichletPartial 3 2 = 9 / 8       := by native_decide
example : dirichletPartial 3 3 = 251 / 216   := by native_decide
example : dirichletPartial 3 4 = 2035 / 1728 := by native_decide

-- ζ(4) partial sums: 1 + 1/16 + 1/81 + ...
example : dirichletPartial 4 1 = 1            := by native_decide
example : dirichletPartial 4 2 = 17 / 16      := by native_decide
example : dirichletPartial 4 3 = 1393 / 1296  := by native_decide

/-! ## 4. Fibonacci numbers and Cassini's identity

  The generating function for Fibonacci numbers is f(z) = z / (1 - z - z^2),
  with radius of convergence ρ = (√5 - 1)/2 ≈ 0.618 (the reciprocal golden ratio).

  Cassini's identity: F_{n-1} · F_{n+1} - F_n^2 = (−1)^n.

  In ℕ arithmetic (no negative numbers):
    • For even n: F_{n-1} · F_{n+1} = F_n^2 - 1  ⟹ written as  F_n^2 = F_{n-1}·F_{n+1} + 1
                                                     Wait, (−1)^{even} = 1,
                                                     so F_{n-1}·F_{n+1} - F_n^2 = 1
                                                     ⟹ F_{n-1}·F_{n+1} = F_n^2 + 1
    • For odd  n: (−1)^{odd} = −1,
                                                     so F_n^2 - F_{n-1}·F_{n+1} = 1
                                                     ⟹ F_n^2 = F_{n-1}·F_{n+1} + 1

  Mathlib uses 0-indexed: Nat.fib 0 = 0, Nat.fib 1 = 1, Nat.fib 2 = 1, ...
  F_6 = 8, F_7 = 13, so Cassini for n = 6 (even):
    F_5 · F_7 - F_6^2 = 5·13 - 64 = 1  ✓                                   -/

-- Cassini identity instances (even n: F_{n-1}·F_{n+1} = F_n^2 + 1? NO)
-- Careful: Cassini says F_{n-1}·F_{n+1} - F_n^2 = (-1)^n.
-- Even n (using 1-based indexing where fib n = F_n):
-- n=2: F_1·F_3 - F_2^2 = 1·2 - 1 = 1 = (-1)^2. ✓
-- n=4: F_3·F_5 - F_4^2 = 2·5 - 9 = 1. ✓
-- n=6: F_5·F_7 - F_6^2 = 5·13 - 64 = 1. ✓
-- Odd n:
-- n=3: F_2·F_4 - F_3^2 = 1·3 - 4 = -1. In ℕ: F_3^2 = F_2·F_4 + 1.
-- n=5: F_4·F_6 - F_5^2 = 3·8 - 25 = -1. In ℕ: F_5^2 = F_4·F_6 + 1.
-- n=7: F_6·F_8 - F_7^2 = 8·21 - 169 = -1. In ℕ: F_7^2 = F_6·F_8 + 1.

-- Even n: F_{n-1}·F_{n+1} = F_n^2 + 1  (Cassini, positive case)
-- Using Mathlib's Nat.fib (0-indexed: fib 0 = 0, fib 1 = 1, fib 2 = 1, fib 3 = 2, ...)
-- So 1-based F_n = Nat.fib n.

-- n=2 (even): Nat.fib 1 * Nat.fib 3 = Nat.fib 2 ^ 2 + 1? No: 1*2 = 2, 1+1=2. Yes!
example : Nat.fib 1 * Nat.fib 3 = Nat.fib 2 ^ 2 + 1 := by native_decide

-- n=4 (even): Nat.fib 3 * Nat.fib 5 = Nat.fib 4 ^ 2 + 1? 2*5=10, 9+1=10. Yes!
example : Nat.fib 3 * Nat.fib 5 = Nat.fib 4 ^ 2 + 1 := by native_decide

-- n=6 (even): Nat.fib 5 * Nat.fib 7 = Nat.fib 6 ^ 2 + 1? 5*13=65, 64+1=65. Yes!
example : Nat.fib 5 * Nat.fib 7 = Nat.fib 6 ^ 2 + 1 := by native_decide

-- n=8 (even): Nat.fib 7 * Nat.fib 9 = Nat.fib 8 ^ 2 + 1? 13*34=442, 441+1=442. Yes!
example : Nat.fib 7 * Nat.fib 9 = Nat.fib 8 ^ 2 + 1 := by native_decide

-- n=10 (even)
example : Nat.fib 9 * Nat.fib 11 = Nat.fib 10 ^ 2 + 1 := by native_decide

-- Odd n: Nat.fib n ^ 2 = Nat.fib (n-1) * Nat.fib (n+1) + 1
-- n=3 (odd): Nat.fib 3^2 = Nat.fib 2 * Nat.fib 4 + 1? 4 = 1*3+1=4. Yes!
example : Nat.fib 3 ^ 2 = Nat.fib 2 * Nat.fib 4 + 1 := by native_decide

-- n=5 (odd): Nat.fib 5^2 = Nat.fib 4 * Nat.fib 6 + 1? 25 = 3*8+1=25. Yes!
example : Nat.fib 5 ^ 2 = Nat.fib 4 * Nat.fib 6 + 1 := by native_decide

-- n=7 (odd): Nat.fib 7^2 = Nat.fib 6 * Nat.fib 8 + 1? 169 = 8*21+1=169. Yes!
example : Nat.fib 7 ^ 2 = Nat.fib 6 * Nat.fib 8 + 1 := by native_decide

-- n=9 (odd)
example : Nat.fib 9 ^ 2 = Nat.fib 8 * Nat.fib 10 + 1 := by native_decide

-- n=11 (odd)
example : Nat.fib 11 ^ 2 = Nat.fib 10 * Nat.fib 12 + 1 := by native_decide

-- Some raw Fibonacci values for reference
example : Nat.fib 0  = 0   := by native_decide
example : Nat.fib 1  = 1   := by native_decide
example : Nat.fib 2  = 1   := by native_decide
example : Nat.fib 3  = 2   := by native_decide
example : Nat.fib 4  = 3   := by native_decide
example : Nat.fib 5  = 5   := by native_decide
example : Nat.fib 6  = 8   := by native_decide
example : Nat.fib 7  = 13  := by native_decide
example : Nat.fib 8  = 21  := by native_decide
example : Nat.fib 9  = 34  := by native_decide
example : Nat.fib 10 = 55  := by native_decide
example : Nat.fib 11 = 89  := by native_decide
example : Nat.fib 12 = 144 := by native_decide

/-! ## 5. GF coefficient extraction: [z^n] 1/(1−2z) = 2^n

  The identity Σ_{k=0}^n r^k = r^{n+1} − 1 confirms that the partial sums of
  the geometric series grow like the dominant pole r.                        -/

-- Powers of 2
example : ∑ k ∈ Finset.range 1,  2 ^ k = 2 ^ 1  - 1 := by native_decide
example : ∑ k ∈ Finset.range 2,  2 ^ k = 2 ^ 2  - 1 := by native_decide
example : ∑ k ∈ Finset.range 3,  2 ^ k = 2 ^ 3  - 1 := by native_decide
example : ∑ k ∈ Finset.range 4,  2 ^ k = 2 ^ 4  - 1 := by native_decide
example : ∑ k ∈ Finset.range 5,  2 ^ k = 2 ^ 5  - 1 := by native_decide
example : ∑ k ∈ Finset.range 6,  2 ^ k = 2 ^ 6  - 1 := by native_decide
example : ∑ k ∈ Finset.range 7,  2 ^ k = 2 ^ 7  - 1 := by native_decide
example : ∑ k ∈ Finset.range 8,  2 ^ k = 2 ^ 8  - 1 := by native_decide
example : ∑ k ∈ Finset.range 9,  2 ^ k = 2 ^ 9  - 1 := by native_decide
example : ∑ k ∈ Finset.range 10, 2 ^ k = 2 ^ 10 - 1 := by native_decide
example : ∑ k ∈ Finset.range 11, 2 ^ k = 2 ^ 11 - 1 := by native_decide

-- Powers of 3: Σ_{k=0}^{n-1} 3^k = (3^n - 1)/2
example : ∑ k ∈ Finset.range 1, 3 ^ k = (3 ^ 1 - 1) / 2 := by native_decide
example : ∑ k ∈ Finset.range 2, 3 ^ k = (3 ^ 2 - 1) / 2 := by native_decide
example : ∑ k ∈ Finset.range 3, 3 ^ k = (3 ^ 3 - 1) / 2 := by native_decide
example : ∑ k ∈ Finset.range 4, 3 ^ k = (3 ^ 4 - 1) / 2 := by native_decide
example : ∑ k ∈ Finset.range 5, 3 ^ k = (3 ^ 5 - 1) / 2 := by native_decide
example : ∑ k ∈ Finset.range 6, 3 ^ k = (3 ^ 6 - 1) / 2 := by native_decide
example : ∑ k ∈ Finset.range 7, 3 ^ k = (3 ^ 7 - 1) / 2 := by native_decide
example : ∑ k ∈ Finset.range 8, 3 ^ k = (3 ^ 8 - 1) / 2 := by native_decide

/-! ## 6. Exponential generating function: [z^n/n!] e^z = 1

  The EGF of the constant sequence (1,1,1,...) is e^z.  Partial sums of
  1/k! give rational approximations to e.

    ePartial n = Σ_{k=0}^n 1/k!                                             -/

def ePartial (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), 1 / (Nat.factorial k : ℚ)

example : ePartial 0 = 1        := by native_decide
example : ePartial 1 = 2        := by native_decide
example : ePartial 2 = 5 / 2    := by native_decide
example : ePartial 3 = 8 / 3    := by native_decide
example : ePartial 4 = 65 / 24  := by native_decide
example : ePartial 5 = 163 / 60 := by native_decide

-- ePartial 5 = 163/60 ≈ 2.7166... is between 2 and 3
example : (2 : ℚ) < ePartial 5  := by native_decide
example : ePartial 5 < 3        := by native_decide

-- A few more terms for fun
example : ePartial 6 = 1957 / 720    := by native_decide
example : ePartial 7 = 685 / 252     := by native_decide
example : ePartial 8 = 109601 / 40320 := by native_decide

-- Each successive partial sum is larger than the previous (monotone convergence)
example : ePartial 0 < ePartial 1 := by native_decide
example : ePartial 1 < ePartial 2 := by native_decide
example : ePartial 2 < ePartial 3 := by native_decide
example : ePartial 3 < ePartial 4 := by native_decide
example : ePartial 4 < ePartial 5 := by native_decide
example : ePartial 5 < ePartial 6 := by native_decide
example : ePartial 6 < ePartial 7 := by native_decide
example : ePartial 7 < ePartial 8 := by native_decide

/-- Geometric Abel-summation sample at base two. -/
theorem geomPartialSum_two_ten :
    geomPartialSum 2 10 = 2 ^ 11 - 1 := by
  native_decide

/-- Cesaro mean sample for an even alternating prefix. -/
theorem cesaroAlt_ten :
    cesaroAlt 10 = 1 / 11 := by
  native_decide

/-- Dirichlet partial sum sample for zeta two. -/
theorem dirichletPartial_two_five :
    dirichletPartial 2 5 = 5269 / 3600 := by
  native_decide

/-- Exponential generating function partial sum sample. -/
theorem ePartial_eight :
    ePartial 8 = 109601 / 40320 := by
  native_decide


structure TauberianTheoremsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TauberianTheoremsBudgetCertificate.controlled
    (c : TauberianTheoremsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def TauberianTheoremsBudgetCertificate.budgetControlled
    (c : TauberianTheoremsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def TauberianTheoremsBudgetCertificate.Ready
    (c : TauberianTheoremsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def TauberianTheoremsBudgetCertificate.size
    (c : TauberianTheoremsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem tauberianTheorems_budgetCertificate_le_size
    (c : TauberianTheoremsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleTauberianTheoremsBudgetCertificate :
    TauberianTheoremsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleTauberianTheoremsBudgetCertificate.Ready := by
  constructor
  · norm_num [TauberianTheoremsBudgetCertificate.controlled,
      sampleTauberianTheoremsBudgetCertificate]
  · norm_num [TauberianTheoremsBudgetCertificate.budgetControlled,
      sampleTauberianTheoremsBudgetCertificate]

example :
    sampleTauberianTheoremsBudgetCertificate.certificateBudgetWindow ≤
      sampleTauberianTheoremsBudgetCertificate.size := by
  apply tauberianTheorems_budgetCertificate_le_size
  constructor
  · norm_num [TauberianTheoremsBudgetCertificate.controlled,
      sampleTauberianTheoremsBudgetCertificate]
  · norm_num [TauberianTheoremsBudgetCertificate.budgetControlled,
      sampleTauberianTheoremsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleTauberianTheoremsBudgetCertificate.Ready := by
  constructor
  · norm_num [TauberianTheoremsBudgetCertificate.controlled,
      sampleTauberianTheoremsBudgetCertificate]
  · norm_num [TauberianTheoremsBudgetCertificate.budgetControlled,
      sampleTauberianTheoremsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleTauberianTheoremsBudgetCertificate.certificateBudgetWindow ≤
      sampleTauberianTheoremsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List TauberianTheoremsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleTauberianTheoremsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleTauberianTheoremsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch4.TauberianTheorems
