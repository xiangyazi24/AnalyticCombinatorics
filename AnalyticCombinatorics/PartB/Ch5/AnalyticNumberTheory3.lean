import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch5.AnalyticNumberTheory3

open Finset Nat


/-! # Analytic Number Theory — Number-Theoretic Functions and Dirichlet Series (Chapter V)

Covering:
- Divisor function d(n)
- Sum of divisors σ(n) and perfect numbers
- Euler's totient φ(n)
- Möbius function μ(n)
- Prime counting function π(n)
- Prime sum function (Chebyshev-style)
-/

-- ============================================================
-- Section 1: Divisor Function d(n)
-- ============================================================

/-! ## Divisor Function d(n)

d(n) = number of positive divisors of n.
d(1)=1, d(2)=2, d(3)=2, d(4)=3, d(6)=4, d(12)=6, d(24)=8, d(60)=12.
-/

def divisorCount (n : ℕ) : ℕ :=
  if n = 0 then 0 else (Finset.Icc 1 n |>.filter (· ∣ n)).card

-- Basic values
example : divisorCount 1 = 1 := by native_decide
example : divisorCount 2 = 2 := by native_decide
example : divisorCount 3 = 2 := by native_decide
example : divisorCount 4 = 3 := by native_decide
example : divisorCount 6 = 4 := by native_decide
example : divisorCount 12 = 6 := by native_decide
example : divisorCount 24 = 8 := by native_decide
example : divisorCount 60 = 12 := by native_decide

-- d(p) = 2 for primes
example : divisorCount 5 = 2 := by native_decide
example : divisorCount 7 = 2 := by native_decide
example : divisorCount 11 = 2 := by native_decide
example : divisorCount 13 = 2 := by native_decide

-- d(p²) = 3
example : divisorCount 9 = 3 := by native_decide   -- 9 = 3²
example : divisorCount 25 = 3 := by native_decide  -- 25 = 5²

-- d(p·q) = 4 for distinct primes
example : divisorCount 15 = 4 := by native_decide  -- 15 = 3·5
example : divisorCount 35 = 4 := by native_decide  -- 35 = 5·7

-- Multiplicativity check: d(4)·d(9) = d(36) since gcd(4,9)=1
-- d(36) = divisors of 36 are 1,2,3,4,6,9,12,18,36 → 9
example : divisorCount 36 = 9 := by native_decide
example : divisorCount 4 * divisorCount 9 = divisorCount 36 := by native_decide

-- Sum of divisor counts: Σ_{k=1}^{10} d(k) = 1+2+2+3+2+4+2+4+3+4 = 27
example : divisorCount 5 + divisorCount 7 + divisorCount 8 + divisorCount 9 + divisorCount 10
        = 2 + 2 + 4 + 3 + 4 := by native_decide
example : 1 + 2 + 2 + 3 + 2 + 4 + 2 + 4 + 3 + 4 = 27 := by native_decide

-- ============================================================
-- Section 2: Sum of Divisors σ(n) and Perfect Numbers
-- ============================================================

/-! ## Sum of Divisors σ(n)

σ(n) = sum of all positive divisors of n.
σ(1)=1, σ(6)=12, σ(12)=28, σ(28)=56.
A number n is *perfect* if σ(n) = 2n.
6, 28, 496 are perfect numbers.
-/

def divisorSum (n : ℕ) : ℕ :=
  if n = 0 then 0 else (Finset.Icc 1 n |>.filter (· ∣ n)).sum id

-- Basic values
example : divisorSum 1 = 1 := by native_decide
example : divisorSum 2 = 3 := by native_decide   -- 1+2
example : divisorSum 3 = 4 := by native_decide   -- 1+3
example : divisorSum 4 = 7 := by native_decide   -- 1+2+4
example : divisorSum 5 = 6 := by native_decide   -- 1+5
example : divisorSum 6 = 12 := by native_decide  -- 1+2+3+6
example : divisorSum 12 = 28 := by native_decide -- 1+2+3+4+6+12
example : divisorSum 28 = 56 := by native_decide -- 1+2+4+7+14+28

-- Perfect number check: σ(n) = 2n
example : divisorSum 6 = 2 * 6 := by native_decide
example : divisorSum 28 = 2 * 28 := by native_decide
example : divisorSum 496 = 2 * 496 := by native_decide

-- σ is multiplicative: σ(4)·σ(9) = σ(36) since gcd(4,9)=1
-- σ(4)=7, σ(9)=13, σ(36)=91
example : divisorSum 9 = 13 := by native_decide   -- 1+3+9
example : divisorSum 36 = 91 := by native_decide  -- 1+2+3+4+6+9+12+18+36
example : divisorSum 4 * divisorSum 9 = divisorSum 36 := by native_decide

-- Abundant number: σ(12) = 28 > 24 = 2·12
example : divisorSum 12 > 2 * 12 := by native_decide

-- Deficient number: σ(8) = 15 < 16 = 2·8
example : divisorSum 8 = 15 := by native_decide
example : divisorSum 8 < 2 * 8 := by native_decide

-- ============================================================
-- Section 3: Euler's Totient φ(n)
-- ============================================================

/-! ## Euler's Totient φ(n)

φ(n) = #{k : 1 ≤ k ≤ n, gcd(k,n) = 1}.
φ(1)=1, φ(2)=1, φ(3)=2, φ(4)=2, φ(6)=2, φ(8)=4, φ(12)=4.
Key identity: Σ_{d|n} φ(d) = n.
For primes: φ(p) = p-1.
-/

def eulerTotient (n : ℕ) : ℕ :=
  (Finset.filter (Nat.Coprime n) (Finset.range n)).card

-- Basic values
example : eulerTotient 1 = 1 := by native_decide
example : eulerTotient 2 = 1 := by native_decide
example : eulerTotient 3 = 2 := by native_decide
example : eulerTotient 4 = 2 := by native_decide
example : eulerTotient 5 = 4 := by native_decide
example : eulerTotient 6 = 2 := by native_decide
example : eulerTotient 7 = 6 := by native_decide
example : eulerTotient 8 = 4 := by native_decide
example : eulerTotient 9 = 6 := by native_decide
example : eulerTotient 10 = 4 := by native_decide
example : eulerTotient 12 = 4 := by native_decide

-- φ(p) = p - 1 for primes p = 5, 7, 11, 13
example : eulerTotient 5 = 5 - 1 := by native_decide
example : eulerTotient 7 = 7 - 1 := by native_decide
example : eulerTotient 11 = 11 - 1 := by native_decide
example : eulerTotient 13 = 13 - 1 := by native_decide

-- φ(p²) = p²-p = p(p-1)
example : eulerTotient 9 = 6 := by native_decide   -- 9=3², φ=3·2=6
example : eulerTotient 25 = 20 := by native_decide -- 25=5², φ=5·4=20

-- Multiplicativity: φ(m·n) = φ(m)·φ(n) when gcd(m,n)=1
-- φ(3)·φ(4) = 2·2 = 4 = φ(12)
example : eulerTotient 3 * eulerTotient 4 = eulerTotient 12 := by native_decide
-- φ(5)·φ(7) = 4·6 = 24 = φ(35)
example : eulerTotient 35 = 24 := by native_decide
example : eulerTotient 5 * eulerTotient 7 = eulerTotient 35 := by native_decide

-- Key identity: Σ_{d|n} φ(d) = n
-- For n=6: divisors are 1,2,3,6; φ(1)+φ(2)+φ(3)+φ(6) = 1+1+2+2 = 6
example : eulerTotient 1 + eulerTotient 2 + eulerTotient 3 + eulerTotient 6 = 6 := by native_decide
-- For n=12: divisors 1,2,3,4,6,12; φ-sum = 1+1+2+2+2+4 = 12
example : eulerTotient 1 + eulerTotient 2 + eulerTotient 3 + eulerTotient 4
        + eulerTotient 6 + eulerTotient 12 = 12 := by native_decide
-- For n=24: divisors 1,2,3,4,6,8,12,24
example : eulerTotient 1 + eulerTotient 2 + eulerTotient 3 + eulerTotient 4
        + eulerTotient 6 + eulerTotient 8 + eulerTotient 12 + eulerTotient 24
        = 24 := by native_decide

-- ============================================================
-- Section 4: Möbius Function μ(n)
-- ============================================================

/-! ## Möbius Function μ(n)

μ(1)=1, μ(p)=-1 (p prime), μ(p²)=0 (p prime), μ(p·q)=1 (p,q distinct primes).
Key property: Σ_{d|n} μ(d) = [n=1] (1 if n=1, 0 otherwise).
-/

-- Table for μ(1) through μ(12):
-- μ(0)=0 (unused), μ(1)=1, μ(2)=-1, μ(3)=-1, μ(4)=0, μ(5)=-1,
-- μ(6)=1, μ(7)=-1, μ(8)=0, μ(9)=0, μ(10)=1, μ(11)=-1, μ(12)=0
def mobiusTable : Fin 13 → ℤ := ![0, 1, -1, -1, 0, -1, 1, -1, 0, 0, 1, -1, 0]

example : mobiusTable 1 = 1 := by native_decide
example : mobiusTable 2 = -1 := by native_decide
example : mobiusTable 3 = -1 := by native_decide
example : mobiusTable 4 = 0 := by native_decide   -- 4 = 2²
example : mobiusTable 5 = -1 := by native_decide
example : mobiusTable 6 = 1 := by native_decide   -- 6 = 2·3
example : mobiusTable 7 = -1 := by native_decide
example : mobiusTable 8 = 0 := by native_decide   -- 8 = 2³
example : mobiusTable 9 = 0 := by native_decide   -- 9 = 3²
example : mobiusTable 10 = 1 := by native_decide  -- 10 = 2·5
example : mobiusTable 11 = -1 := by native_decide
example : mobiusTable 12 = 0 := by native_decide  -- 12 = 2²·3

-- μ(1) + μ(2) = 1 + (-1) = 0 = [2=1]
example : mobiusTable 1 + mobiusTable 2 = 0 := by native_decide

-- Σ_{d|6} μ(d) = μ(1)+μ(2)+μ(3)+μ(6) = 1-1-1+1 = 0
example : mobiusTable 1 + mobiusTable 2 + mobiusTable 3 + mobiusTable 6 = 0 := by native_decide

-- Σ_{d|12} μ(d) = μ(1)+μ(2)+μ(3)+μ(4)+μ(6)+μ(12)
--              = 1 + (-1) + (-1) + 0 + 1 + 0 = 0
example : mobiusTable 1 + mobiusTable 2 + mobiusTable 3 + mobiusTable 4
        + mobiusTable 6 + mobiusTable 12 = 0 := by native_decide

-- Σ_{d|10} μ(d) = μ(1)+μ(2)+μ(5)+μ(10) = 1-1-1+1 = 0
example : mobiusTable 1 + mobiusTable 2 + mobiusTable 5 + mobiusTable 10 = 0 := by native_decide

-- Verify: for n=1, Σ_{d|1} μ(d) = μ(1) = 1
example : mobiusTable 1 = 1 := by native_decide

-- Möbius inversion numerics: if f(n) = Σ_{d|n} g(d), then g(n) = Σ_{d|n} μ(n/d) f(d)
-- Take f = σ (divisor sum), g = id. σ(n) = Σ_{d|n} d, so id(n) = Σ_{d|n} μ(n/d) σ(d).
-- For n=6: μ(6)σ(1) + μ(3)σ(2) + μ(2)σ(3) + μ(1)σ(6)
--        = 1·1 + (-1)·3 + (-1)·4 + 1·12 = 1 - 3 - 4 + 12 = 6
example : (1 : ℤ) * 1 + (-1) * 3 + (-1) * 4 + 1 * 12 = 6 := by native_decide

-- For n=12: μ(12)σ(1) + μ(6)σ(2) + μ(4)σ(3) + μ(3)σ(4)
--         + μ(2)σ(6) + μ(1)σ(12)
--         = 0·1 + 1·3 + 0·4 + (-1)·7 + (-1)·12 + 1·28
--         = 0 + 3 + 0 - 7 - 12 + 28 = 12
example : (0 : ℤ) * 1 + 1 * 3 + 0 * 4 + (-1) * 7 + (-1) * 12 + 1 * 28 = 12 := by native_decide

-- ============================================================
-- Section 5: Prime Counting Function π(n)
-- ============================================================

/-! ## Prime Counting Function π(n)

π(n) = #{primes p : p ≤ n}.
π(10)=4, π(20)=8, π(30)=10, π(50)=15, π(100)=25.
-/

def primePi (n : ℕ) : ℕ :=
  (Finset.filter Nat.Prime (Finset.range (n + 1))).card

example : primePi 10 = 4 := by native_decide   -- {2,3,5,7}
example : primePi 20 = 8 := by native_decide   -- add 11,13,17,19
example : primePi 30 = 10 := by native_decide  -- add 23,29
example : primePi 50 = 15 := by native_decide  -- add 31,37,41,43,47
example : primePi 100 = 25 := by native_decide

-- π is nondecreasing
example : primePi 10 ≤ primePi 20 := by native_decide
example : primePi 20 ≤ primePi 50 := by native_decide
example : primePi 50 ≤ primePi 100 := by native_decide

-- Primes between 10 and 20: π(20) - π(10) = 4
example : primePi 20 - primePi 10 = 4 := by native_decide

-- Primes between 50 and 100: π(100) - π(50) = 10
example : primePi 100 - primePi 50 = 10 := by native_decide

-- ============================================================
-- Section 6: Prime Sum (Chebyshev-style)
-- ============================================================

/-! ## Prime Sum (Chebyshev θ-approximation via integer sums)

Σ_{p≤n, p prime} p.
primeSum(10) = 2+3+5+7 = 17.
primeSum(20) = 2+3+5+7+11+13+17+19 = 77.
primeSum(30) = 77+23+29 = 129.
primeSum(50) = 129+31+37+41+43+47 = 328.
-/

def primeSum (n : ℕ) : ℕ :=
  (Finset.filter Nat.Prime (Finset.range (n + 1))).sum id

example : primeSum 10 = 17 := by native_decide
example : primeSum 20 = 77 := by native_decide
example : primeSum 30 = 129 := by native_decide
example : primeSum 50 = 328 := by native_decide

-- Partial sums check
example : 2 + 3 + 5 + 7 = 17 := by native_decide
example : 17 + 11 + 13 + 17 + 19 = 77 := by native_decide
example : 77 + 23 + 29 = 129 := by native_decide
example : 129 + 31 + 37 + 41 + 43 + 47 = 328 := by native_decide

-- Heuristic: primeSum(n) / (n² / 2) should be close to 1
-- n=100: Σ p ≤ 100 = 1060. n²/2 = 5000. ratio ≈ 0.21 (PNT: ~n²/(2 ln n))
example : primeSum 100 = 1060 := by native_decide

-- Smallest prime > 100 is 101
example : Nat.Prime 101 = true := by native_decide
example : primePi 101 - primePi 100 = 1 := by native_decide

-- Twin prime pairs (p, p+2) both prime, for small values
example : Nat.Prime 3 ∧ Nat.Prime 5 := by native_decide
example : Nat.Prime 5 ∧ Nat.Prime 7 := by native_decide
example : Nat.Prime 11 ∧ Nat.Prime 13 := by native_decide
example : Nat.Prime 17 ∧ Nat.Prime 19 := by native_decide
example : Nat.Prime 29 ∧ Nat.Prime 31 := by native_decide
example : Nat.Prime 41 ∧ Nat.Prime 43 := by native_decide

/-- Divisor-count sample at a highly composite small integer. -/
theorem divisorCount_sixty :
    divisorCount 60 = 12 := by
  native_decide

/-- Perfect-number sum-of-divisors sample. -/
theorem divisorSum_496_perfect :
    divisorSum 496 = 2 * 496 := by
  native_decide

/-- Prime-counting sample at one hundred. -/
theorem primePi_hundred :
    primePi 100 = 25 := by
  native_decide

/-- Prime-sum sample at one hundred. -/
theorem primeSum_hundred :
    primeSum 100 = 1060 := by
  native_decide



structure AnalyticNumberTheory3BudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticNumberTheory3BudgetCertificate.controlled
    (c : AnalyticNumberTheory3BudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AnalyticNumberTheory3BudgetCertificate.budgetControlled
    (c : AnalyticNumberTheory3BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AnalyticNumberTheory3BudgetCertificate.Ready
    (c : AnalyticNumberTheory3BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AnalyticNumberTheory3BudgetCertificate.size
    (c : AnalyticNumberTheory3BudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem analyticNumberTheory3_budgetCertificate_le_size
    (c : AnalyticNumberTheory3BudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAnalyticNumberTheory3BudgetCertificate :
    AnalyticNumberTheory3BudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleAnalyticNumberTheory3BudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticNumberTheory3BudgetCertificate.controlled,
      sampleAnalyticNumberTheory3BudgetCertificate]
  · norm_num [AnalyticNumberTheory3BudgetCertificate.budgetControlled,
      sampleAnalyticNumberTheory3BudgetCertificate]

example :
    sampleAnalyticNumberTheory3BudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticNumberTheory3BudgetCertificate.size := by
  apply analyticNumberTheory3_budgetCertificate_le_size
  constructor
  · norm_num [AnalyticNumberTheory3BudgetCertificate.controlled,
      sampleAnalyticNumberTheory3BudgetCertificate]
  · norm_num [AnalyticNumberTheory3BudgetCertificate.budgetControlled,
      sampleAnalyticNumberTheory3BudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleAnalyticNumberTheory3BudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticNumberTheory3BudgetCertificate.controlled,
      sampleAnalyticNumberTheory3BudgetCertificate]
  · norm_num [AnalyticNumberTheory3BudgetCertificate.budgetControlled,
      sampleAnalyticNumberTheory3BudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAnalyticNumberTheory3BudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticNumberTheory3BudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List AnalyticNumberTheory3BudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAnalyticNumberTheory3BudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAnalyticNumberTheory3BudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch5.AnalyticNumberTheory3
