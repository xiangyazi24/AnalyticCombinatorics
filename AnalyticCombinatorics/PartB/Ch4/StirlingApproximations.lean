/-
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter IV — Stirling Approximations

  Verified numerical identities related to:
  • Factorial super-exponential growth rates
  • Wilson's theorem: (p-1)! ≡ -1 (mod p) for prime p
  • Double factorial definition and identities
  • Superfactorial definition and values
  • Catalan number growth bounds
  • Ratio identities for factorials and central binomial coefficients
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch4.StirlingApproximations
/-! ## 1. Factorial super-exponential growth

  Stirling's approximation: n! ~ √(2πn) · (n/e)^n.
  We verify that n! grows faster than exponentials. -/

/-- 10! > 3^10 -/
example : Nat.factorial 10 > 3 ^ 10 := by native_decide

/-- 15! > 10^10 -/
example : Nat.factorial 15 > 10 ^ 10 := by native_decide

/-- 20! > 10^17 -/
example : Nat.factorial 20 > 10 ^ 17 := by native_decide

/-- 12! > 4^12 -/
example : Nat.factorial 12 > 4 ^ 12 := by native_decide

/-- 10! > 2^16 -/
example : Nat.factorial 10 > 2 ^ 16 := by native_decide

/-! ## 2. Wilson's theorem: (p-1)! ≡ p-1 (mod p) for prime p

  Equivalently, (p-1)! ≡ -1 (mod p). Since we work in ℕ,
  we verify (p-1)! % p = p-1. -/

/-- (7-1)! ≡ 6 (mod 7): Wilson's theorem for p=7. -/
example : Nat.factorial 6 % 7 = 6 := by native_decide

/-- (11-1)! ≡ 10 (mod 11): Wilson's theorem for p=11. -/
example : Nat.factorial 10 % 11 = 10 := by native_decide

/-- (13-1)! ≡ 12 (mod 13): Wilson's theorem for p=13. -/
example : Nat.factorial 12 % 13 = 12 := by native_decide

/-- (17-1)! ≡ 16 (mod 17): Wilson's theorem for p=17. -/
example : Nat.factorial 16 % 17 = 16 := by native_decide

/-- (5-1)! ≡ 4 (mod 5): Wilson's theorem for p=5. -/
example : Nat.factorial 4 % 5 = 4 := by native_decide

/-- (3-1)! ≡ 2 (mod 3): Wilson's theorem for p=3. -/
example : Nat.factorial 2 % 3 = 2 := by native_decide

/-! ## 3. Double factorial

  The double factorial n!! is defined by:
    0!! = 1,  1!! = 1,  n!! = n · (n-2)!!  for n ≥ 2.
  Even values: (2n)!! = 2^n · n!
  Odd values: (2n-1)!! = (2n)! / ((2n)!! ) = (2n)! / (2^n · n!) -/

/-- Double factorial: n!! -/
def doubleFact : ℕ → ℕ
  | 0     => 1
  | 1     => 1
  | n + 2 => (n + 2) * doubleFact n
  decreasing_by omega

/-- doubleFact 0 = 1 -/
example : doubleFact 0 = 1 := by native_decide

/-- doubleFact 1 = 1 -/
example : doubleFact 1 = 1 := by native_decide

/-- doubleFact 2 = 2 -/
example : doubleFact 2 = 2 := by native_decide

/-- doubleFact 3 = 3 -/
example : doubleFact 3 = 3 := by native_decide

/-- doubleFact 4 = 8 -/
example : doubleFact 4 = 8 := by native_decide

/-- doubleFact 5 = 15 -/
example : doubleFact 5 = 15 := by native_decide

/-- doubleFact 6 = 48 -/
example : doubleFact 6 = 48 := by native_decide

/-- doubleFact 7 = 105 -/
example : doubleFact 7 = 105 := by native_decide

/-- doubleFact 8 = 384 -/
example : doubleFact 8 = 384 := by native_decide

/-! ### 3a. Even double factorial identity: (2n)!! = 2^n · n!

  We verify doubleFact (2*n) = 2^n * n! for n = 1..5. -/

/-- doubleFact 2 = 2^1 * 1! -/
example : doubleFact 2 = 2 ^ 1 * Nat.factorial 1 := by native_decide

/-- doubleFact 4 = 2^2 * 2! -/
example : doubleFact 4 = 2 ^ 2 * Nat.factorial 2 := by native_decide

/-- doubleFact 6 = 2^3 * 3! -/
example : doubleFact 6 = 2 ^ 3 * Nat.factorial 3 := by native_decide

/-- doubleFact 8 = 2^4 * 4! -/
example : doubleFact 8 = 2 ^ 4 * Nat.factorial 4 := by native_decide

/-- doubleFact 10 = 2^5 * 5! -/
example : doubleFact 10 = 2 ^ 5 * Nat.factorial 5 := by native_decide

/-! ### 3b. Factorial splitting: (2n)! = (2n)!! * (2n-1)!!

  We verify Nat.factorial (2*n) = doubleFact (2*n) * doubleFact (2*n-1)
  for small concrete values. -/

/-- 2! = 2!! * 1!! = 2 * 1 = 2 -/
example : Nat.factorial 2 = doubleFact 2 * doubleFact 1 := by native_decide

/-- 4! = 4!! * 3!! = 8 * 3 = 24 -/
example : Nat.factorial 4 = doubleFact 4 * doubleFact 3 := by native_decide

/-- 6! = 6!! * 5!! = 48 * 15 = 720 -/
example : Nat.factorial 6 = doubleFact 6 * doubleFact 5 := by native_decide

/-- 8! = 8!! * 7!! = 384 * 105 = 40320 -/
example : Nat.factorial 8 = doubleFact 8 * doubleFact 7 := by native_decide

/-- 10! = 10!! * 9!! -/
example : Nat.factorial 10 = doubleFact 10 * doubleFact 9 := by native_decide

/-! ## 4. Superfactorial

  The superfactorial is sf(n) = ∏_{k=1}^{n} k! = 1! · 2! · 3! · … · n!.
  Using Finset.range n and shifting the index: sf(n) = ∏ k ∈ Finset.range n, (k+1)!. -/

/-- Superfactorial sf(n) = ∏_{k=1}^{n} k! -/
def superFact (n : ℕ) : ℕ := ∏ k ∈ Finset.range n, Nat.factorial (k + 1)

/-- sf(1) = 1! = 1 -/
example : superFact 1 = 1 := by native_decide

/-- sf(2) = 1! * 2! = 2 -/
example : superFact 2 = 2 := by native_decide

/-- sf(3) = 1! * 2! * 3! = 12 -/
example : superFact 3 = 12 := by native_decide

/-- sf(4) = 1! * 2! * 3! * 4! = 288 -/
example : superFact 4 = 288 := by native_decide

/-- sf(5) = 1! * 2! * 3! * 4! * 5! = 34560 -/
example : superFact 5 = 34560 := by native_decide

/-! ## 5. Catalan number growth

  The n-th Catalan number satisfies C_n = C(2n,n)/(n+1).
  Asymptotically C_n ~ 4^n / (n^{3/2} · √π).
  We verify the bounds 4^n / (2n) < C(2n,n) < 4^n. -/

/-- Upper bound: 4^5 > C(10,5) = 252 -/
example : 4 ^ 5 > Nat.choose 10 5 := by native_decide

/-- Lower bound: C(10,5) * 10 > 4^5, i.e. 2520 > 1024 -/
example : Nat.choose 10 5 * 10 > 4 ^ 5 := by native_decide

/-- Upper bound: 4^6 > C(12,6) = 924 -/
example : 4 ^ 6 > Nat.choose 12 6 := by native_decide

/-- Lower bound: C(12,6) * 12 > 4^6, i.e. 11088 > 4096 -/
example : Nat.choose 12 6 * 12 > 4 ^ 6 := by native_decide

/-- Odd double-factorial quotient for perfect matchings. -/
def oddDoubleFactorialQuotient (n : ℕ) : ℕ :=
  Nat.factorial (2 * n) / (2 ^ n * Nat.factorial n)

theorem oddDoubleFactorialQuotient_five :
    oddDoubleFactorialQuotient 5 = 945 := by
  native_decide

/-- Central-binomial Stirling envelope. -/
def centralBinomialEnvelope (n : ℕ) : ℕ :=
  4 ^ n

theorem centralBinomialEnvelope_six :
    Nat.choose 12 6 < centralBinomialEnvelope 6 := by
  native_decide

/-- Upper bound: 4^7 > C(14,7) = 3432 -/
example : 4 ^ 7 > Nat.choose 14 7 := by native_decide

/-- Lower bound: C(14,7) * 14 > 4^7, i.e. 48048 > 16384 -/
example : Nat.choose 14 7 * 14 > 4 ^ 7 := by native_decide

/-- Upper bound: 4^8 > C(16,8) = 12870 -/
example : 4 ^ 8 > Nat.choose 16 8 := by native_decide

/-- Lower bound: C(16,8) * 16 > 4^8, i.e. 205920 > 65536 -/
example : Nat.choose 16 8 * 16 > 4 ^ 8 := by native_decide

/-! ## 6. Ratio of consecutive factorials

  Since (n+1)! = (n+1) · n!, the ratio is exactly n+1. -/

/-- 10!/9! = 10 -/
example : Nat.factorial 10 / Nat.factorial 9 = 10 := by native_decide

/-- 15!/14! = 15 -/
example : Nat.factorial 15 / Nat.factorial 14 = 15 := by native_decide

/-- 20!/19! = 20 -/
example : Nat.factorial 20 / Nat.factorial 19 = 20 := by native_decide

/-- 7!/6! = 7 -/
example : Nat.factorial 7 / Nat.factorial 6 = 7 := by native_decide

/-! ## 7. Central binomial coefficient recurrence

  The central binomial coefficients satisfy the recurrence
    C(2n+2, n+1) = C(2n, n) · 2(2n+1)/(n+1).
  In integer form: C(2n+2, n+1) · (n+1) = C(2n, n) · 2·(2n+1).
  Equivalently: C(2(n+1), n+1) · (n+1) = C(2n, n) · (4n+2). -/

/-- For n=1: C(4,2) * 2 = C(2,1) * 6, i.e. 6*2 = 2*6 = 12. -/
example : Nat.choose 4 2 * 2 = Nat.choose 2 1 * 6 := by native_decide

/-- For n=2: C(6,3) * 3 = C(4,2) * 10, i.e. 20*3 = 6*10 = 60. -/
example : Nat.choose 6 3 * 3 = Nat.choose 4 2 * 10 := by native_decide

/-- For n=3: C(8,4) * 4 = C(6,3) * 14, i.e. 70*4 = 20*14 = 280. -/
example : Nat.choose 8 4 * 4 = Nat.choose 6 3 * 14 := by native_decide

/-- For n=4: C(10,5) * 5 = C(8,4) * 18, i.e. 252*5 = 70*18 = 1260. -/
example : Nat.choose 10 5 * 5 = Nat.choose 8 4 * 18 := by native_decide

/-- For n=5: C(12,6) * 6 = C(10,5) * 22, i.e. 924*6 = 252*22 = 5544. -/
example : Nat.choose 12 6 * 6 = Nat.choose 10 5 * 22 := by native_decide

/-- For n=6: C(14,7) * 7 = C(12,6) * 26, i.e. 3432*7 = 924*26 = 24024. -/
example : Nat.choose 14 7 * 7 = Nat.choose 12 6 * 26 := by native_decide

/-- For n=7: C(16,8) * 8 = C(14,7) * 30, i.e. 12870*8 = 3432*30 = 102960. -/
example : Nat.choose 16 8 * 8 = Nat.choose 14 7 * 30 := by native_decide


structure StirlingApproximationsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def StirlingApproximationsBudgetCertificate.controlled
    (c : StirlingApproximationsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def StirlingApproximationsBudgetCertificate.budgetControlled
    (c : StirlingApproximationsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def StirlingApproximationsBudgetCertificate.Ready
    (c : StirlingApproximationsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def StirlingApproximationsBudgetCertificate.size
    (c : StirlingApproximationsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem stirlingApproximations_budgetCertificate_le_size
    (c : StirlingApproximationsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleStirlingApproximationsBudgetCertificate :
    StirlingApproximationsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleStirlingApproximationsBudgetCertificate.Ready := by
  constructor
  · norm_num [StirlingApproximationsBudgetCertificate.controlled,
      sampleStirlingApproximationsBudgetCertificate]
  · norm_num [StirlingApproximationsBudgetCertificate.budgetControlled,
      sampleStirlingApproximationsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleStirlingApproximationsBudgetCertificate.certificateBudgetWindow ≤
      sampleStirlingApproximationsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleStirlingApproximationsBudgetCertificate.Ready := by
  constructor
  · norm_num [StirlingApproximationsBudgetCertificate.controlled,
      sampleStirlingApproximationsBudgetCertificate]
  · norm_num [StirlingApproximationsBudgetCertificate.budgetControlled,
      sampleStirlingApproximationsBudgetCertificate]

example :
    sampleStirlingApproximationsBudgetCertificate.certificateBudgetWindow ≤
      sampleStirlingApproximationsBudgetCertificate.size := by
  apply stirlingApproximations_budgetCertificate_le_size
  constructor
  · norm_num [StirlingApproximationsBudgetCertificate.controlled,
      sampleStirlingApproximationsBudgetCertificate]
  · norm_num [StirlingApproximationsBudgetCertificate.budgetControlled,
      sampleStirlingApproximationsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List StirlingApproximationsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleStirlingApproximationsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleStirlingApproximationsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch4.StirlingApproximations
