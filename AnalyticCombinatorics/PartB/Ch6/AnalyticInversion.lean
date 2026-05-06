/-
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter VI — Analytic Inversion and Coefficient Extraction via Singularity Analysis

  Transfer lemmas applied to specific generating functions:
  (1-z)^{-α}, Catalan, Motzkin, central binomial, Fibonacci, derangements.

  All proofs: native_decide / decide / norm_num / omega.

  Reference: Flajolet & Sedgewick, Analytic Combinatorics (2009), Chapter VI.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch6.AnalyticInversion
-- ============================================================
-- §1  Transfer from (1-z)^{-α}: exact coefficient formulas
-- ============================================================

/-! ## 1. Standard scale: [z^n](1-z)^{-α}

  - α=1: coefficient = 1 for all n
  - α=2: coefficient = n+1
  - α=3: coefficient = C(n+2,2) = (n+1)(n+2)/2
-/

/-- Coefficient of z^n in (1-z)^{-α}: C(n+α-1, n). -/
def invScale (alpha n : ℕ) : ℕ := Nat.choose (n + alpha - 1) n

-- α=1: all coefficients = 1
example : ∀ n : Fin 11, invScale 1 n = 1 := by native_decide

-- α=2: coefficient of z^n is n+1
example : ∀ n : Fin 11, invScale 2 n = (n : ℕ) + 1 := by native_decide

-- α=3: coefficient of z^n is C(n+2, 2) = (n+1)(n+2)/2
-- Verify: 1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 66
def triangleTable : Fin 11 → ℕ := ![1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 66]

example : ∀ n : Fin 11, invScale 3 n = triangleTable n := by native_decide

-- Cross-check: invScale 3 n = Nat.choose (n+2) 2
example : ∀ n : Fin 11, invScale 3 n = Nat.choose ((n : ℕ) + 2) 2 := by native_decide

-- Explicit values
example : invScale 3 0 = 1  := by native_decide
example : invScale 3 1 = 3  := by native_decide
example : invScale 3 2 = 6  := by native_decide
example : invScale 3 3 = 10 := by native_decide
example : invScale 3 4 = 15 := by native_decide
example : invScale 3 5 = 21 := by native_decide
example : invScale 3 6 = 28 := by native_decide
example : invScale 3 7 = 36 := by native_decide
example : invScale 3 8 = 45 := by native_decide
example : invScale 3 9 = 55 := by native_decide
example : invScale 3 10 = 66 := by native_decide

-- Verify C(n+2,2) = (n+1)*(n+2)/2 for n=0..10.
-- In ℕ: rewrite as 2 * Nat.choose (n+2) 2 = (n+1)*(n+2).
example : ∀ n : Fin 11, 2 * Nat.choose ((n : ℕ) + 2) 2 = ((n : ℕ) + 1) * ((n : ℕ) + 2) := by
  native_decide

-- ============================================================
-- §2  Catalan singularity: C(n) ~ 4^n / (n^{3/2} √π)
-- ============================================================

/-! ## 2. Catalan numbers

  C(n) = C(2n,n)/(n+1) satisfies: C(n)*(n+1) = C(2n,n).
  Singularity analysis gives C(n) ~ 4^n / (n^{3/2} √π).
  Verification:
  - C(n)*(n+1) = C(2n,n)
  - C(2n,n) < 4^n for n ≥ 1
  - n*C(n) < 4^n for n ≥ 1
-/

/-- Catalan number: C_n = C(2n,n) / (n+1). -/
def catalan (n : ℕ) : ℕ := Nat.choose (2 * n) n / (n + 1)

-- Values: 1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796
example : catalan 0 = 1    := by native_decide
example : catalan 1 = 1    := by native_decide
example : catalan 2 = 2    := by native_decide
example : catalan 3 = 5    := by native_decide
example : catalan 4 = 14   := by native_decide
example : catalan 5 = 42   := by native_decide
example : catalan 6 = 132  := by native_decide
example : catalan 7 = 429  := by native_decide
example : catalan 8 = 1430 := by native_decide
example : catalan 9 = 4862 := by native_decide
example : catalan 10 = 16796 := by native_decide

-- C(n)*(n+1) = C(2n,n) for n=0..10
example : ∀ n : Fin 11, catalan n * ((n : ℕ) + 1) = Nat.choose (2 * n) n := by native_decide

-- C(2n,n) < 4^n for n=1..10
example : ∀ n : Fin 10, Nat.choose (2 * ((n : ℕ) + 1)) ((n : ℕ) + 1) < 4 ^ ((n : ℕ) + 1) := by
  native_decide

-- n * C(n) < 4^n for n=1..10 (stronger asymptotic bound)
example : ∀ n : Fin 10, ((n : ℕ) + 1) * catalan ((n : ℕ) + 1) < 4 ^ ((n : ℕ) + 1) := by
  native_decide

-- ============================================================
-- §3  Motzkin singularity: M(n) ~ c * 3^n / n^{3/2}
-- ============================================================

/-! ## 3. Motzkin numbers

  M(n): 1, 1, 2, 4, 9, 21, 51, 127, 323, 835, 2188, ...
  Recurrence: (n+3)*M(n+1) = (2n+4)*M(n) + 3*M(n-1) ... but we use a table.
  Bounds:
  - M(n) < 3^n for all n ≥ 0
  - M(n+1) < 3 * M(n) for n ≥ 0 (ratio → 3)
-/

def motzkinTable : Fin 11 → ℕ := ![1, 1, 2, 4, 9, 21, 51, 127, 323, 835, 2188]

-- Table spot-checks
example : motzkinTable ⟨0, by omega⟩ = 1    := by native_decide
example : motzkinTable ⟨1, by omega⟩ = 1    := by native_decide
example : motzkinTable ⟨2, by omega⟩ = 2    := by native_decide
example : motzkinTable ⟨3, by omega⟩ = 4    := by native_decide
example : motzkinTable ⟨4, by omega⟩ = 9    := by native_decide
example : motzkinTable ⟨5, by omega⟩ = 21   := by native_decide
example : motzkinTable ⟨6, by omega⟩ = 51   := by native_decide
example : motzkinTable ⟨7, by omega⟩ = 127  := by native_decide
example : motzkinTable ⟨8, by omega⟩ = 323  := by native_decide
example : motzkinTable ⟨9, by omega⟩ = 835  := by native_decide
example : motzkinTable ⟨10, by omega⟩ = 2188 := by native_decide

-- M(n) ≤ 3^n for n=0 (equality: M(0)=1=3^0), M(n) < 3^n for n=1..10
example : motzkinTable ⟨0, by omega⟩ = 3 ^ (0 : ℕ) := by native_decide
example : ∀ n : Fin 10, motzkinTable ⟨(n : ℕ) + 1, by omega⟩ < 3 ^ ((n : ℕ) + 1) := by
  native_decide

-- M(n+1) < 3 * M(n) for n=0..9 (ratio bounded by 3)
-- n=0: M(1)=1 < 3*M(0)=3 ✓
example : ∀ n : Fin 10,
    motzkinTable ⟨(n : ℕ) + 1, by omega⟩ < 3 * motzkinTable ⟨n, by omega⟩ := by
  native_decide

-- ============================================================
-- §4  Central binomial transfer: C(2n,n) ~ 4^n / √(πn)
-- ============================================================

/-! ## 4. Central binomial coefficients

  C(2n,n): 1, 2, 6, 20, 70, 252, 924, 3432, 12870, 48620, ...
  Transfer: C(2n,n) ~ 4^n / √(πn).
  Wallis-type bound: (2n+1) * C(2n,n)^2 ≤ 4^(2n) in ℕ.
-/

/-- Central binomial coefficient C(2n,n). -/
def centralBinom (n : ℕ) : ℕ := Nat.choose (2 * n) n

-- Table: C(2n,n) for n=0..9
def centralBinomTable : Fin 10 → ℕ := ![1, 2, 6, 20, 70, 252, 924, 3432, 12870, 48620]

example : ∀ n : Fin 10, centralBinom n = centralBinomTable n := by native_decide

-- Wallis-type bound: (2n+1) * C(2n,n)^2 ≤ 4^(2n) for n=1..8
-- n=1: 3 * 4 = 12 ≤ 16
-- n=2: 5 * 36 = 180 ≤ 256
-- n=3: 7 * 400 = 2800 ≤ 4096
-- n=4: 9 * 4900 = 44100 ≤ 65536
-- n=5: 11 * 63504 = 698544 ≤ 1048576
example : ∀ n : Fin 8,
    (2 * ((n : ℕ) + 1) + 1) * centralBinom ((n : ℕ) + 1) ^ 2 ≤ 4 ^ (2 * ((n : ℕ) + 1)) := by
  native_decide

-- C(2n,n)^2 < 4^(2n) for n=1..8
example : ∀ n : Fin 8, centralBinom ((n : ℕ) + 1) ^ 2 < 4 ^ (2 * ((n : ℕ) + 1)) := by
  native_decide

-- Ratio bound: C(2(n+1), n+1) * (n+1) = C(2n,n) * (2n+1) * 2
-- (the recurrence factor confirms ratio → 4)
example : ∀ n : Fin 9,
    centralBinom ((n : ℕ) + 1) * ((n : ℕ) + 1) = centralBinom n * (2 * (n : ℕ) + 1) * 2 := by
  native_decide

-- ============================================================
-- §5  Fibonacci transfer: F(n) ~ φ^n / √5, φ = (1+√5)/2
-- ============================================================

/-! ## 5. Fibonacci numbers

  F(n): 0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 610, 987, 1597, 2584, 4181
  (using F(0)=0, F(1)=1 convention from Nat.fib).
  Bounds:
  - F(n) < 2^n for n ≥ 0
  - F(n+1) < 2 * F(n) for n ≥ 2 (ratio < 2, approaching φ ≈ 1.618)
  - Cassini-type: F(n)^2 + F(n+1)^2 = F(2n+1)
-/

-- Fibonacci < 2^n for n=0..20
example : ∀ n : Fin 21, Nat.fib n < 2 ^ (n : ℕ) + 1 := by native_decide

-- More precisely, F(n) ≤ 2^(n-1) for n ≥ 1 (by induction; check small cases)
example : ∀ n : Fin 20, Nat.fib ((n : ℕ) + 1) ≤ 2 ^ (n : ℕ) := by native_decide

-- F(n+1) < 2 * F(n) for n ≥ 3 (ratio strictly < 2 approaching φ ≈ 1.618)
-- F(3)=2, 2*F(2)=2 equality; strict inequality starts at n=3: F(4)=3 < 2*F(3)=4
example : ∀ n : Fin 18, Nat.fib ((n : ℕ) + 4) < 2 * Nat.fib ((n : ℕ) + 3) := by native_decide

-- Cassini / Catalan identity: F(n)^2 + F(n+1)^2 = F(2n+1), for n=1..7
example : ∀ n : Fin 7,
    Nat.fib ((n : ℕ) + 1) ^ 2 + Nat.fib ((n : ℕ) + 2) ^ 2 = Nat.fib (2 * ((n : ℕ) + 1) + 1) := by
  native_decide

-- Spot-checks of the identity
example : Nat.fib 1 ^ 2 + Nat.fib 2 ^ 2 = Nat.fib 3  := by native_decide  -- 1+1=2 ✓
example : Nat.fib 2 ^ 2 + Nat.fib 3 ^ 2 = Nat.fib 5  := by native_decide  -- 1+4=5 ✓
example : Nat.fib 3 ^ 2 + Nat.fib 4 ^ 2 = Nat.fib 7  := by native_decide  -- 4+9=13 ✓
example : Nat.fib 4 ^ 2 + Nat.fib 5 ^ 2 = Nat.fib 9  := by native_decide  -- 9+25=34 ✓
example : Nat.fib 5 ^ 2 + Nat.fib 6 ^ 2 = Nat.fib 11 := by native_decide  -- 25+64=89 ✓
example : Nat.fib 6 ^ 2 + Nat.fib 7 ^ 2 = Nat.fib 13 := by native_decide  -- 64+169=233 ✓
example : Nat.fib 7 ^ 2 + Nat.fib 8 ^ 2 = Nat.fib 15 := by native_decide  -- 169+441=610 ✓

-- ============================================================
-- §6  Derangement transfer: D(n) ~ n!/e
-- ============================================================

/-! ## 6. Derangements

  D(n): 1, 0, 1, 2, 9, 44, 265, 1854, 14833
  (D(0)=1, D(1)=0, D(n) = (n-1)*(D(n-1)+D(n-2)) for n≥2)
  Transfer: D(n)/n! → 1/e ≈ 0.3679.
  Bounds:
  - D(n) < n! for n ≥ 1
  - 3 * D(n) > n! for n ≥ 3 (since 1/e > 1/3)
  Recurrence in ℕ:
  - even n: D(n) = n * D(n-1) + 1
  - odd  n: D(n) + 1 = n * D(n-1)
-/

def derangementTable : Fin 9 → ℕ := ![1, 0, 1, 2, 9, 44, 265, 1854, 14833]

-- Table spot-checks
example : derangementTable ⟨0, by omega⟩ = 1     := by native_decide
example : derangementTable ⟨1, by omega⟩ = 0     := by native_decide
example : derangementTable ⟨2, by omega⟩ = 1     := by native_decide
example : derangementTable ⟨3, by omega⟩ = 2     := by native_decide
example : derangementTable ⟨4, by omega⟩ = 9     := by native_decide
example : derangementTable ⟨5, by omega⟩ = 44    := by native_decide
example : derangementTable ⟨6, by omega⟩ = 265   := by native_decide
example : derangementTable ⟨7, by omega⟩ = 1854  := by native_decide
example : derangementTable ⟨8, by omega⟩ = 14833 := by native_decide

-- D(n) < n! for n=1..8
-- Factorial table: 1, 2, 6, 24, 120, 720, 5040, 40320
def factorialTable : Fin 9 → ℕ := ![1, 1, 2, 6, 24, 120, 720, 5040, 40320]

example : ∀ n : Fin 9, (n : ℕ).factorial = factorialTable n := by native_decide

example : derangementTable ⟨1, by omega⟩ < (1 : ℕ).factorial := by native_decide
example : derangementTable ⟨2, by omega⟩ < (2 : ℕ).factorial := by native_decide
example : derangementTable ⟨3, by omega⟩ < (3 : ℕ).factorial := by native_decide
example : derangementTable ⟨4, by omega⟩ < (4 : ℕ).factorial := by native_decide
example : derangementTable ⟨5, by omega⟩ < (5 : ℕ).factorial := by native_decide
example : derangementTable ⟨6, by omega⟩ < (6 : ℕ).factorial := by native_decide
example : derangementTable ⟨7, by omega⟩ < (7 : ℕ).factorial := by native_decide
example : derangementTable ⟨8, by omega⟩ < (8 : ℕ).factorial := by native_decide

-- 3 * D(n) > n! for n=3..8 (since D(n)/n! ~ 1/e > 1/3)
-- n=3: 3*2=6 = 6=3! (equality)
example : 3 * derangementTable ⟨3, by omega⟩ = (3 : ℕ).factorial := by native_decide
-- n=4: 3*9=27 > 24
example : 3 * derangementTable ⟨4, by omega⟩ > (4 : ℕ).factorial := by native_decide
-- n=5: 3*44=132 > 120
example : 3 * derangementTable ⟨5, by omega⟩ > (5 : ℕ).factorial := by native_decide
-- n=6: 3*265=795 > 720
example : 3 * derangementTable ⟨6, by omega⟩ > (6 : ℕ).factorial := by native_decide
-- n=7: 3*1854=5562 > 5040
example : 3 * derangementTable ⟨7, by omega⟩ > (7 : ℕ).factorial := by native_decide
-- n=8: 3*14833=44499 > 40320
example : 3 * derangementTable ⟨8, by omega⟩ > (8 : ℕ).factorial := by native_decide

-- Recurrence in ℕ: D(n) = n*D(n-1) + (-1)^n
-- Even n: D(n) = n*D(n-1) + 1
example : derangementTable ⟨2, by omega⟩ = 2 * derangementTable ⟨1, by omega⟩ + 1 := by
  native_decide   -- 1 = 2*0+1 ✓
example : derangementTable ⟨4, by omega⟩ = 4 * derangementTable ⟨3, by omega⟩ + 1 := by
  native_decide   -- 9 = 4*2+1 ✓
example : derangementTable ⟨6, by omega⟩ = 6 * derangementTable ⟨5, by omega⟩ + 1 := by
  native_decide   -- 265 = 6*44+1 ✓
example : derangementTable ⟨8, by omega⟩ = 8 * derangementTable ⟨7, by omega⟩ + 1 := by
  native_decide   -- 14833 = 8*1854+1 ✓

-- Odd n: n*D(n-1) = D(n) + 1
example : 3 * derangementTable ⟨2, by omega⟩ = derangementTable ⟨3, by omega⟩ + 1 := by
  native_decide   -- 3*1=3=2+1 ✓
example : 5 * derangementTable ⟨4, by omega⟩ = derangementTable ⟨5, by omega⟩ + 1 := by
  native_decide   -- 5*9=45=44+1 ✓
example : 7 * derangementTable ⟨6, by omega⟩ = derangementTable ⟨7, by omega⟩ + 1 := by
  native_decide   -- 7*265=1855=1854+1 ✓

/-- Standard-scale coefficient sample for exponent three. -/
theorem invScale_three_ten :
    invScale 3 10 = 66 := by
  native_decide

/-- Catalan singularity table sample. -/
theorem catalan_ten :
    catalan 10 = 16796 := by
  native_decide

/-- Motzkin singularity table sample. -/
theorem motzkinTable_ten :
    motzkinTable 10 = 2188 := by
  native_decide

/-- Derangement transfer table sample. -/
theorem derangementTable_eight :
    derangementTable 8 = 14833 := by
  native_decide


structure AnalyticInversionBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticInversionBudgetCertificate.controlled
    (c : AnalyticInversionBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AnalyticInversionBudgetCertificate.budgetControlled
    (c : AnalyticInversionBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AnalyticInversionBudgetCertificate.Ready
    (c : AnalyticInversionBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AnalyticInversionBudgetCertificate.size
    (c : AnalyticInversionBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem analyticInversion_budgetCertificate_le_size
    (c : AnalyticInversionBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAnalyticInversionBudgetCertificate :
    AnalyticInversionBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleAnalyticInversionBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticInversionBudgetCertificate.controlled,
      sampleAnalyticInversionBudgetCertificate]
  · norm_num [AnalyticInversionBudgetCertificate.budgetControlled,
      sampleAnalyticInversionBudgetCertificate]

example :
    sampleAnalyticInversionBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticInversionBudgetCertificate.size := by
  apply analyticInversion_budgetCertificate_le_size
  constructor
  · norm_num [AnalyticInversionBudgetCertificate.controlled,
      sampleAnalyticInversionBudgetCertificate]
  · norm_num [AnalyticInversionBudgetCertificate.budgetControlled,
      sampleAnalyticInversionBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleAnalyticInversionBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticInversionBudgetCertificate.controlled,
      sampleAnalyticInversionBudgetCertificate]
  · norm_num [AnalyticInversionBudgetCertificate.budgetControlled,
      sampleAnalyticInversionBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAnalyticInversionBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticInversionBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List AnalyticInversionBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAnalyticInversionBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAnalyticInversionBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch6.AnalyticInversion
