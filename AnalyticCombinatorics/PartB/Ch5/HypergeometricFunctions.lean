/-
  Analytic Combinatorics — Part B
  Chapter V — Hypergeometric Functions

  Numerical verifications of hypergeometric function identities used in
  analytic combinatorics: Pochhammer symbols, central binomial coefficients,
  Chu–Vandermonde convolution, Catalan numbers, Motzkin numbers, Gauss 2F1
  summation, and the falling factorial / binomial connection.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch5.HypergeometricFunctions
open Finset

/-! ## 1. Pochhammer symbol (rising factorial) -/

/-- Pochhammer symbol: (a)_n = a(a+1)···(a+n-1). -/
def pochhammer (a n : ℕ) : ℕ := ∏ i ∈ Finset.range n, (a + i)

/-- (a)_0 = 1 (empty product). Verified for a = 0..9. -/
example : pochhammer 0 0 = 1 := by native_decide
example : pochhammer 1 0 = 1 := by native_decide
example : pochhammer 2 0 = 1 := by native_decide
example : pochhammer 5 0 = 1 := by native_decide
example : pochhammer 9 0 = 1 := by native_decide

/-- (1)_n = n!  Verify for n = 0..7. -/
example : pochhammer 1 0 = Nat.factorial 0 := by native_decide
example : pochhammer 1 1 = Nat.factorial 1 := by native_decide
example : pochhammer 1 2 = Nat.factorial 2 := by native_decide
example : pochhammer 1 3 = Nat.factorial 3 := by native_decide
example : pochhammer 1 4 = Nat.factorial 4 := by native_decide
example : pochhammer 1 5 = Nat.factorial 5 := by native_decide
example : pochhammer 1 6 = Nat.factorial 6 := by native_decide
example : pochhammer 1 7 = Nat.factorial 7 := by native_decide

/-- (3)_4 = 3·4·5·6 = 360. -/
example : pochhammer 3 4 = 360 := by native_decide

/-- (2)_5 = 2·3·4·5·6 = 720. -/
example : pochhammer 2 5 = 720 := by native_decide

/-- (5)_3 = 5·6·7 = 210. -/
example : pochhammer 5 3 = 210 := by native_decide

/-- (1)_n = n! as a general Nat.factorial connection (n = 10). -/
example : pochhammer 1 10 = Nat.factorial 10 := by native_decide

/-! ## 2. Central binomial coefficients -/

/-- C(2n,n) table: n = 0..7 gives 1, 2, 6, 20, 70, 252, 924, 3432. -/
example : Nat.choose 0 0 = 1   := by native_decide
example : Nat.choose 2 1 = 2   := by native_decide
example : Nat.choose 4 2 = 6   := by native_decide
example : Nat.choose 6 3 = 20  := by native_decide
example : Nat.choose 8 4 = 70  := by native_decide
example : Nat.choose 10 5 = 252  := by native_decide
example : Nat.choose 12 6 = 924  := by native_decide
example : Nat.choose 14 7 = 3432 := by native_decide

/-- Additional values. -/
example : Nat.choose 20 10 = 184756 := by native_decide
example : Nat.choose 16 8  = 12870  := by native_decide

/-- C(2n,n) = (2n)! / (n!)²  — verify for n = 4:
    C(8,4) = 8! / (4!)² = 40320 / 576 = 70. -/
example : Nat.factorial 8 / (Nat.factorial 4 * Nat.factorial 4) = 70 := by native_decide

/-- C(2n,n) = (2n)! / (n!)²  — verify for n = 5. -/
example : Nat.factorial 10 / (Nat.factorial 5 * Nat.factorial 5) = 252 := by native_decide

/-- Symmetry check: C(2n,n) = C(2n, 2n-n). -/
example : Nat.choose 10 5 = Nat.choose 10 5 := by native_decide

/-- Growth check: 4^4 | (4·C(8,4)) via the ratio 4^n / C(2n,n) ≈ √(πn).
    Numerically: 4^4 = 256 and 256 / 70 is not an integer;
    instead verify 4^n * (n+1) > C(2n,n) for n=4: 256*5 = 1280 > 70. -/
example : 4^4 * 5 > Nat.choose 8 4 := by native_decide

/-! ## 3. Chu–Vandermonde identity -/

/-- Verify C(7,3) = Σ_{k=0}^3 C(4,k)·C(3, 3-k).
    Chu-Vandermonde: C(m+n, r) = sum_{k=0}^r C(m,k)*C(n, r-k).
    m=4, n=3, r=3: C(7,3) = C(4,0)C(3,3)+C(4,1)C(3,2)+C(4,2)C(3,1)+C(4,3)C(3,0)
    = 1·1 + 4·3 + 6·3 + 4·1 = 1+12+18+4 = 35. -/
example : Nat.choose 7 3 =
    ∑ k ∈ Finset.range 4,
      Nat.choose 4 k * Nat.choose 3 (if k ≤ 3 then 3 - k else 0) := by native_decide

/-- Verify C(10,4) = Σ_{k=0}^4 C(6,k)·C(4, 4-k).
    m=6, n=4, r=4. -/
example : Nat.choose 10 4 =
    ∑ k ∈ Finset.range 5,
      Nat.choose 6 k * Nat.choose 4 (if k ≤ 4 then 4 - k else 0) := by native_decide

/-- Verify C(9,5) = Σ_{k=0}^5 C(5,k)·C(4, 5-k). -/
example : Nat.choose 9 5 =
    ∑ k ∈ Finset.range 6,
      Nat.choose 5 k * Nat.choose 4 (if k ≤ 5 then 5 - k else 0) := by native_decide

/-- Vandermonde special case: Σ_{k=0}^n C(n,k)² = C(2n,n).
    (Set m = n, r = n.) Verify for n=4. -/
example : ∑ k ∈ Finset.range 5, Nat.choose 4 k * Nat.choose 4 k = Nat.choose 8 4 := by
  native_decide

/-- Same identity for n=5. -/
example : ∑ k ∈ Finset.range 6, Nat.choose 5 k * Nat.choose 5 k = Nat.choose 10 5 := by
  native_decide

/-! ## 4. Catalan numbers via central binomials -/

/-- Catalan number by central binomial: C_n = C(2n,n) / (n+1). -/
def catalanCB (n : ℕ) : ℕ := Nat.choose (2 * n) n / (n + 1)

/-- Verify C_n for n = 0..8: 1, 1, 2, 5, 14, 42, 132, 429, 1430. -/
example : catalanCB 0 = 1    := by native_decide
example : catalanCB 1 = 1    := by native_decide
example : catalanCB 2 = 2    := by native_decide
example : catalanCB 3 = 5    := by native_decide
example : catalanCB 4 = 14   := by native_decide
example : catalanCB 5 = 42   := by native_decide
example : catalanCB 6 = 132  := by native_decide
example : catalanCB 7 = 429  := by native_decide
example : catalanCB 8 = 1430 := by native_decide

/-- Ballot-problem formula: C_n = C(2n,n) - C(2n, n+1).
    Verify for n=0..5. -/
example : Nat.choose 0 0 - Nat.choose 0 1 = 1   := by native_decide
example : Nat.choose 2 1 - Nat.choose 2 2 = 1   := by native_decide
example : Nat.choose 4 2 - Nat.choose 4 3 = 2   := by native_decide
example : Nat.choose 6 3 - Nat.choose 6 4 = 5   := by native_decide
example : Nat.choose 8 4 - Nat.choose 8 5 = 14  := by native_decide
example : Nat.choose 10 5 - Nat.choose 10 6 = 42 := by native_decide

/-- Consistency: catalanCB agrees with ballot formula for n=4..7. -/
example : catalanCB 4 = Nat.choose 8 4  - Nat.choose 8 5  := by native_decide
example : catalanCB 5 = Nat.choose 10 5 - Nat.choose 10 6 := by native_decide
example : catalanCB 6 = Nat.choose 12 6 - Nat.choose 12 7 := by native_decide
example : catalanCB 7 = Nat.choose 14 7 - Nat.choose 14 8 := by native_decide

/-! ## 5. Motzkin numbers via hypergeometric sum -/

/-- Motzkin number: M_n = Σ_{k=0}^{⌊n/2⌋} C(n, 2k)·C_k. -/
def motzkinHyp (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n / 2 + 1), Nat.choose n (2 * k) * catalanCB k

/-- Verify M_n for n = 0..6: 1, 1, 2, 4, 9, 21, 51. -/
example : motzkinHyp 0 = 1  := by native_decide
example : motzkinHyp 1 = 1  := by native_decide
example : motzkinHyp 2 = 2  := by native_decide
example : motzkinHyp 3 = 4  := by native_decide
example : motzkinHyp 4 = 9  := by native_decide
example : motzkinHyp 5 = 21 := by native_decide
example : motzkinHyp 6 = 51 := by native_decide

/-- Motzkin recurrence: (n+2)·M_n = (2n+1)·M_{n-1} + 3·(n-1)·M_{n-2}  for n ≥ 2.
    Verify for n = 2..6 using concrete values. -/
example : 4 * motzkinHyp 2 = 5 * motzkinHyp 1 + 3 * 1 * motzkinHyp 0 := by native_decide
example : 5 * motzkinHyp 3 = 7 * motzkinHyp 2 + 3 * 2 * motzkinHyp 1 := by native_decide
example : 6 * motzkinHyp 4 = 9 * motzkinHyp 3 + 3 * 3 * motzkinHyp 2 := by native_decide
example : 7 * motzkinHyp 5 = 11 * motzkinHyp 4 + 3 * 4 * motzkinHyp 3 := by native_decide
example : 8 * motzkinHyp 6 = 13 * motzkinHyp 5 + 3 * 5 * motzkinHyp 4 := by native_decide

/-! ## 6. Gauss 2F1: binomial–Pochhammer connection -/

/-- Falling factorial: fallingFact n k = n·(n-1)···(n-k+1) in ℕ.
    When k > n this truncates to 0 via Nat subtraction. -/
def fallingFact (n k : ℕ) : ℕ := ∏ i ∈ Finset.range k, (n - i)

/-- fallingFact 6 3 = 6·5·4 = 120. -/
example : fallingFact 6 3 = 120 := by native_decide

/-- Equivalently: C(6,3)·3! = 20·6 = 120. -/
example : Nat.choose 6 3 * Nat.factorial 3 = 120 := by native_decide

/-- Consistency: fallingFact 6 3 = C(6,3)·3!. -/
example : fallingFact 6 3 = Nat.choose 6 3 * Nat.factorial 3 := by native_decide

/-- fallingFact 10 4 = 10·9·8·7 = 5040. -/
example : fallingFact 10 4 = 5040 := by native_decide

/-- C(10,4)·4! = 210·24 = 5040. -/
example : Nat.choose 10 4 * Nat.factorial 4 = 5040 := by native_decide

/-- Consistency: fallingFact 10 4 = C(10,4)·4!. -/
example : fallingFact 10 4 = Nat.choose 10 4 * Nat.factorial 4 := by native_decide

/-- General falling–binomial connection for several more pairs. -/
example : fallingFact 7 3 = Nat.choose 7 3 * Nat.factorial 3 := by native_decide
example : fallingFact 8 5 = Nat.choose 8 5 * Nat.factorial 5 := by native_decide
example : fallingFact 12 4 = Nat.choose 12 4 * Nat.factorial 4 := by native_decide

/-- Vanishing: fallingFact n k = 0 when k > n (natural-number underflow → product hits 0).
    E.g. fallingFact 3 4 = 3·2·1·0 = 0. -/
example : fallingFact 3 4 = 0 := by native_decide
example : fallingFact 2 5 = 0 := by native_decide

/-- Gauss 2F1 terminating case: 2F1(-n, 1; 1; 1) = (1-1)_n/(1)_n counts to 0 for n≥1,
    or more usefully 2F1(-n, b; b; 1) = Σ_{k=0}^n C(n,k)(-1)^k = 0 for n≥1.
    Verify via integer arithmetic in ℤ for n=4:
    Σ_{k=0}^4 C(4,k)·(-1)^k = 1-4+6-4+1 = 0. -/
example : (1 : ℤ) - 4 + 6 - 4 + 1 = 0 := by native_decide

/-- Same for n=6: Σ C(6,k)(-1)^k = 1-6+15-20+15-6+1 = 0. -/
example : (1 : ℤ) - 6 + 15 - 20 + 15 - 6 + 1 = 0 := by native_decide

/-- Kummer's theorem specialisation: 2F1(-n, n+1; 2; 1) = 1/(n+1) (scaled).
    Here we verify the scaled integer form (n+1)·C_n = C(2n,n) for n=0..5. -/
example : 1 * catalanCB 0 = Nat.choose 0 0   := by native_decide
example : 2 * catalanCB 1 = Nat.choose 2 1   := by native_decide
example : 3 * catalanCB 2 = Nat.choose 4 2   := by native_decide
example : 4 * catalanCB 3 = Nat.choose 6 3   := by native_decide
example : 5 * catalanCB 4 = Nat.choose 8 4   := by native_decide
example : 6 * catalanCB 5 = Nat.choose 10 5  := by native_decide

/-- Pochhammer-to-binomial ratio identity:
    C(n,k) = (n)_k / k!  as natural numbers (falling version).
    Equivalently fallingFact n k = C(n,k) · k!.
    Checked via pochhammer rising: (n-k+1)_k = fallingFact n k for k ≤ n.
    Verify for (n,k)=(7,3): risingFact(5,3) = 5·6·7 = 210 = fallingFact 7 3. -/
def risingFact (a n : ℕ) : ℕ := ∏ i ∈ Finset.range n, (a + i)

example : risingFact 5 3 = fallingFact 7 3 := by native_decide
example : risingFact 7 4 = fallingFact 10 4 := by native_decide
example : risingFact 6 5 = fallingFact 10 5 := by native_decide

/-- Pochhammer sample. -/
theorem pochhammer_two_five :
    pochhammer 2 5 = 720 := by
  native_decide

/-- Catalan central-binomial sample. -/
theorem catalanCB_eight :
    catalanCB 8 = 1430 := by
  native_decide

/-- Motzkin hypergeometric sample. -/
theorem motzkinHyp_six :
    motzkinHyp 6 = 51 := by
  native_decide

/-- Falling-rising factorial bridge sample. -/
theorem risingFact_fallingFact_sample :
    risingFact 7 4 = fallingFact 10 4 := by
  native_decide


structure HypergeometricFunctionsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def HypergeometricFunctionsBudgetCertificate.controlled
    (c : HypergeometricFunctionsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def HypergeometricFunctionsBudgetCertificate.budgetControlled
    (c : HypergeometricFunctionsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def HypergeometricFunctionsBudgetCertificate.Ready
    (c : HypergeometricFunctionsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def HypergeometricFunctionsBudgetCertificate.size
    (c : HypergeometricFunctionsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem hypergeometricFunctions_budgetCertificate_le_size
    (c : HypergeometricFunctionsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleHypergeometricFunctionsBudgetCertificate :
    HypergeometricFunctionsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleHypergeometricFunctionsBudgetCertificate.Ready := by
  constructor
  · norm_num [HypergeometricFunctionsBudgetCertificate.controlled,
      sampleHypergeometricFunctionsBudgetCertificate]
  · norm_num [HypergeometricFunctionsBudgetCertificate.budgetControlled,
      sampleHypergeometricFunctionsBudgetCertificate]

example :
    sampleHypergeometricFunctionsBudgetCertificate.certificateBudgetWindow ≤
      sampleHypergeometricFunctionsBudgetCertificate.size := by
  apply hypergeometricFunctions_budgetCertificate_le_size
  constructor
  · norm_num [HypergeometricFunctionsBudgetCertificate.controlled,
      sampleHypergeometricFunctionsBudgetCertificate]
  · norm_num [HypergeometricFunctionsBudgetCertificate.budgetControlled,
      sampleHypergeometricFunctionsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleHypergeometricFunctionsBudgetCertificate.Ready := by
  constructor
  · norm_num [HypergeometricFunctionsBudgetCertificate.controlled,
      sampleHypergeometricFunctionsBudgetCertificate]
  · norm_num [HypergeometricFunctionsBudgetCertificate.budgetControlled,
      sampleHypergeometricFunctionsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleHypergeometricFunctionsBudgetCertificate.certificateBudgetWindow ≤
      sampleHypergeometricFunctionsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List HypergeometricFunctionsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleHypergeometricFunctionsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleHypergeometricFunctionsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch5.HypergeometricFunctions
