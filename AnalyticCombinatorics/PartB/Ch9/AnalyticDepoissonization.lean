import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AnalyticDepoissonization

/-!
# Analytic Depoissonization

Poissonization–depoissonization from Flajolet–Sedgewick,
*Analytic Combinatorics*, Chapter IX. Given exact-size coefficients fₙ,
the Poisson GF is T(z) = e^{-z} Σ fₙ zⁿ/n!. Exact depoissonization
recovers fₙ via finite differences of the EGF. The analytic version
(Theorem IX.8) gives fₙ ~ T(n) under I/O growth conditions in cones.
-/

open Finset

/-! ## 1. Poisson weights -/

/-- Poisson weight: z^k / k! as a rational. -/
def poissonWeight (z k : ℕ) : ℚ :=
  (z : ℚ) ^ k / (Nat.factorial k : ℚ)

/-- Partial exponential sum: Σ_{k=0}^{N} z^k / k!. -/
def partialExp (z N : ℕ) : ℚ :=
  ∑ k ∈ range (N + 1), poissonWeight z k

theorem poisson_weight_z3 :
    poissonWeight 3 0 = 1 ∧ poissonWeight 3 1 = 3 ∧
    poissonWeight 3 2 = 9 / 2 ∧ poissonWeight 3 3 = 9 / 2 ∧
    poissonWeight 3 4 = 27 / 8 ∧ poissonWeight 3 5 = 81 / 40 := by native_decide

theorem poisson_weight_z2 :
    poissonWeight 2 0 = 1 ∧ poissonWeight 2 1 = 2 ∧
    poissonWeight 2 2 = 2 ∧ poissonWeight 2 3 = 4 / 3 ∧
    poissonWeight 2 4 = 2 / 3 ∧ poissonWeight 2 5 = 4 / 15 := by native_decide

theorem partial_exp_values :
    partialExp 1 4 = 65 / 24 ∧
    partialExp 2 5 = 109 / 15 ∧
    partialExp 3 5 = 92 / 5 := by native_decide

/-! ## 2. Partial EGF (Poissonization) -/

/-- Partial EGF of sequence f at integer z, truncated at degree N:
    Σ_{m=0}^{N} f(m) · z^m / m!. -/
def partialEGF (f : ℕ → ℚ) (N z : ℕ) : ℚ :=
  ∑ m ∈ range (N + 1), f m * poissonWeight z m

theorem egf_const_is_exp :
    partialEGF (fun _ => 1) 5 2 = 109 / 15 ∧
    partialEGF (fun _ => 1) 4 1 = 65 / 24 := by native_decide

theorem egf_linear_values :
    partialEGF (fun n => (n : ℚ)) 4 1 = 8 / 3 ∧
    partialEGF (fun n => (n : ℚ)) 4 2 = 38 / 3 ∧
    partialEGF (fun n => (n : ℚ)) 4 3 = 39 := by native_decide

/-! ## 3. Finite differences and exact depoissonization -/

/-- Alternating sign: (-1)^m. -/
def altSign (m : ℕ) : ℚ :=
  if m % 2 = 0 then 1 else -1

/-- Signed binomial coefficient: (-1)^{n-k} · C(n,k). -/
def signedBinom (n k : ℕ) : ℚ :=
  altSign (n - k) * (Nat.choose n k : ℚ)

/-- n-th finite difference of f at 0:
    Δⁿf(0) = Σ_{k=0}^{n} (-1)^{n-k} C(n,k) f(k). -/
def finiteDiff (f : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ k ∈ range (n + 1), signedBinom n k * f k

/-- Exact depoissonization: recover f(n) from integer-point
    samples of its EGF via n-th order finite differences. -/
def depoissonExact (f : ℕ → ℚ) (n : ℕ) : ℚ :=
  finiteDiff (fun k => partialEGF f n k) n

/-- Δⁿ[x^m](0): equals n! when m = n, and 0 when m < n. -/
def finiteDiffPower (m n : ℕ) : ℚ :=
  finiteDiff (fun k => (k : ℚ) ^ m) n

theorem finite_diff_diagonal :
    finiteDiffPower 0 0 = 1 ∧ finiteDiffPower 1 1 = 1 ∧
    finiteDiffPower 2 2 = 2 ∧ finiteDiffPower 3 3 = 6 ∧
    finiteDiffPower 4 4 = 24 := by native_decide

theorem finite_diff_below_diagonal :
    finiteDiffPower 0 1 = 0 ∧ finiteDiffPower 0 2 = 0 ∧
    finiteDiffPower 1 2 = 0 ∧ finiteDiffPower 1 3 = 0 ∧
    finiteDiffPower 2 3 = 0 := by native_decide

theorem depoisson_const :
    depoissonExact (fun _ => (1 : ℚ)) 0 = 1 ∧
    depoissonExact (fun _ => (1 : ℚ)) 1 = 1 ∧
    depoissonExact (fun _ => (1 : ℚ)) 2 = 1 ∧
    depoissonExact (fun _ => (1 : ℚ)) 3 = 1 := by native_decide

theorem depoisson_linear :
    depoissonExact (fun n => (n : ℚ)) 0 = 0 ∧
    depoissonExact (fun n => (n : ℚ)) 1 = 1 ∧
    depoissonExact (fun n => (n : ℚ)) 2 = 2 ∧
    depoissonExact (fun n => (n : ℚ)) 3 = 3 := by native_decide

theorem depoisson_quadratic :
    depoissonExact (fun n => (n : ℚ) ^ 2) 0 = 0 ∧
    depoissonExact (fun n => (n : ℚ) ^ 2) 1 = 1 ∧
    depoissonExact (fun n => (n : ℚ) ^ 2) 2 = 4 ∧
    depoissonExact (fun n => (n : ℚ) ^ 2) 3 = 9 := by native_decide

theorem depoisson_factorial :
    depoissonExact (fun n => (Nat.factorial n : ℚ)) 0 = 1 ∧
    depoissonExact (fun n => (Nat.factorial n : ℚ)) 1 = 1 ∧
    depoissonExact (fun n => (Nat.factorial n : ℚ)) 2 = 2 ∧
    depoissonExact (fun n => (Nat.factorial n : ℚ)) 3 = 6 := by native_decide

theorem depoisson_exponential :
    depoissonExact (fun n => (2 : ℚ) ^ n) 0 = 1 ∧
    depoissonExact (fun n => (2 : ℚ) ^ n) 1 = 2 ∧
    depoissonExact (fun n => (2 : ℚ) ^ n) 2 = 4 ∧
    depoissonExact (fun n => (2 : ℚ) ^ n) 3 = 8 := by native_decide

/-- Algebraic depoissonization identity: finite differences of the EGF
    always recover the original sequence exactly. -/
theorem depoissonExact_recovers (f : ℕ → ℚ) (n : ℕ) :
    depoissonExact f n = f n := by
  sorry

/-! ## 4. Stirling numbers via finite differences -/

/-- Stirling number S(m,n) via the finite-difference formula:
    S(m,n) = Δⁿ[x^m](0) / n!. Complements the recurrence definition
    in Depoissonization.lean with the explicit inclusion-exclusion form. -/
def stirling2FD (m n : ℕ) : ℚ :=
  finiteDiffPower m n / (Nat.factorial n : ℚ)

theorem stirling2FD_triangle :
    stirling2FD 0 0 = 1 ∧
    stirling2FD 1 1 = 1 ∧
    stirling2FD 2 1 = 1 ∧ stirling2FD 2 2 = 1 ∧
    stirling2FD 3 1 = 1 ∧ stirling2FD 3 2 = 3 ∧ stirling2FD 3 3 = 1 ∧
    stirling2FD 4 1 = 1 ∧ stirling2FD 4 2 = 7 ∧
    stirling2FD 4 3 = 6 ∧ stirling2FD 4 4 = 1 := by native_decide

theorem stirling2FD_bell_numbers :
    stirling2FD 3 1 + stirling2FD 3 2 + stirling2FD 3 3 = 5 ∧
    stirling2FD 4 1 + stirling2FD 4 2 + stirling2FD 4 3 +
      stirling2FD 4 4 = 15 := by native_decide

/-! ## 5. Growth conditions for analytic depoissonization -/

/-- I-condition: |T(z)| ≤ C|z|^α inside cone |arg(z)| < θ, θ > π/2. -/
structure ICondition where
  coneHalfAngle : ℚ
  growthExponent : ℚ
  bound : ℚ

/-- O-condition: |T(z)·e^z| ≤ C·e^{a|z|} outside cone, with a < 1. -/
structure OCondition where
  coneHalfAngle : ℚ
  decayRate : ℚ
  bound : ℚ

/-- Combined depoissonization conditions (Theorem IX.8). -/
structure DepoissonCond where
  inner : ICondition
  outer : OCondition

def exampleCond : DepoissonCond where
  inner := { coneHalfAngle := 2, growthExponent := 1, bound := 10 }
  outer := { coneHalfAngle := 2, decayRate := 1 / 2, bound := 10 }

example : exampleCond.outer.decayRate < 1 := by native_decide
example : exampleCond.inner.coneHalfAngle > 157 / 100 := by native_decide

end AnalyticDepoissonization
