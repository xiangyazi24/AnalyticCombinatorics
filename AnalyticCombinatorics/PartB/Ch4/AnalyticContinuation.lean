/-
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter IV — Analytic Continuation and Coefficient Extraction

  Formalized coefficient sequences from partial fractions, linear recurrences,
  Lucas numbers, the Fibonacci-Lucas identity, and exponential polynomials.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticContinuation

/-! ## 1. Coefficient from partial fractions

  [z^n] 1/((1-2z)(1-3z)) = 3^{n+1} - 2^{n+1}
-/

/-- The coefficient of z^n in 1/((1-2z)(1-3z)) by partial fractions. -/
def twoThreeCoeff (n : ℕ) : ℤ := 3 ^ (n + 1) - 2 ^ (n + 1)

theorem twoThreeCoeff_0 : twoThreeCoeff 0 = 1 := by native_decide
theorem twoThreeCoeff_1 : twoThreeCoeff 1 = 5 := by native_decide
theorem twoThreeCoeff_2 : twoThreeCoeff 2 = 19 := by native_decide
theorem twoThreeCoeff_3 : twoThreeCoeff 3 = 65 := by native_decide
theorem twoThreeCoeff_4 : twoThreeCoeff 4 = 211 := by native_decide

/-! ## 2. Linear recurrence from characteristic polynomial

  a_n = 3*a_{n-1} - 2*a_{n-2}   (characteristic polynomial: x² - 3x + 2 = (x-1)(x-2))
-/

/-- Linear recurrence a_n = 3*a_{n-1} - 2*a_{n-2} with given initial values. -/
def linearRec (a0 a1 : ℤ) : ℕ → ℤ
  | 0 => a0
  | 1 => a1
  | n + 2 => 3 * linearRec a0 a1 (n + 1) - 2 * linearRec a0 a1 n
decreasing_by all_goals omega

/-- With a0=0, a1=1: linearRec gives 2^n - 1. -/
theorem linearRec_01_val0 : linearRec 0 1 0 = 2 ^ 0 - 1 := by native_decide
theorem linearRec_01_val1 : linearRec 0 1 1 = 2 ^ 1 - 1 := by native_decide
theorem linearRec_01_val2 : linearRec 0 1 2 = 2 ^ 2 - 1 := by native_decide
theorem linearRec_01_val3 : linearRec 0 1 3 = 2 ^ 3 - 1 := by native_decide
theorem linearRec_01_val4 : linearRec 0 1 4 = 2 ^ 4 - 1 := by native_decide
theorem linearRec_01_val5 : linearRec 0 1 5 = 2 ^ 5 - 1 := by native_decide
theorem linearRec_01_val6 : linearRec 0 1 6 = 2 ^ 6 - 1 := by native_decide

/-- With a0=2, a1=3: linearRec gives 1 + 2^n. -/
theorem linearRec_23_val0 : linearRec 2 3 0 = 1 + 2 ^ 0 := by native_decide
theorem linearRec_23_val1 : linearRec 2 3 1 = 1 + 2 ^ 1 := by native_decide
theorem linearRec_23_val2 : linearRec 2 3 2 = 1 + 2 ^ 2 := by native_decide
theorem linearRec_23_val3 : linearRec 2 3 3 = 1 + 2 ^ 3 := by native_decide

/-! ## 3. Lucas numbers -/

/-- The Lucas sequence: L_0 = 2, L_1 = 1, L_{n+2} = L_{n+1} + L_n. -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => lucas (n + 1) + lucas n
decreasing_by all_goals omega

theorem lucas_0 : lucas 0 = 2 := by native_decide
theorem lucas_1 : lucas 1 = 1 := by native_decide
theorem lucas_2 : lucas 2 = 3 := by native_decide
theorem lucas_3 : lucas 3 = 4 := by native_decide
theorem lucas_4 : lucas 4 = 7 := by native_decide
theorem lucas_5 : lucas 5 = 11 := by native_decide
theorem lucas_6 : lucas 6 = 18 := by native_decide

/-! ## 4. Fibonacci-Lucas identity: L_n² - 5·F_n² = 4·(-1)^n -/

/-- Boolean check of the Fibonacci-Lucas identity L_n² - 5·F_n² = 4·(-1)^n. -/
def fibLucasIdentityCheck (n : ℕ) : Bool :=
  (lucas n : ℤ) ^ 2 - 5 * (Nat.fib n : ℤ) ^ 2 == 4 * (-1 : ℤ) ^ n

theorem fibLucas_identity_0 : fibLucasIdentityCheck 0 = true := by native_decide
theorem fibLucas_identity_1 : fibLucasIdentityCheck 1 = true := by native_decide
theorem fibLucas_identity_2 : fibLucasIdentityCheck 2 = true := by native_decide
theorem fibLucas_identity_3 : fibLucasIdentityCheck 3 = true := by native_decide
theorem fibLucas_identity_4 : fibLucasIdentityCheck 4 = true := by native_decide
theorem fibLucas_identity_5 : fibLucasIdentityCheck 5 = true := by native_decide
theorem fibLucas_identity_6 : fibLucasIdentityCheck 6 = true := by native_decide
theorem fibLucas_identity_7 : fibLucasIdentityCheck 7 = true := by native_decide
theorem fibLucas_identity_8 : fibLucasIdentityCheck 8 = true := by native_decide

/-! ## 5. Exponential polynomial: n·2^n satisfies a_n = 4·a_{n-1} - 4·a_{n-2} -/

/-- The sequence n·2^n. -/
def expPolySeq (n : ℕ) : ℕ := n * 2 ^ n

/-- Boolean check that n·2^n satisfies the recurrence a_n = 4·a_{n-1} - 4·a_{n-2}. -/
def expPolyRecCheck (n : ℕ) : Bool :=
  n ≥ 2 && (expPolySeq n : ℤ) == 4 * (expPolySeq (n - 1) : ℤ) - 4 * (expPolySeq (n - 2) : ℤ)

theorem expPoly_rec_2 : expPolyRecCheck 2 = true := by native_decide
theorem expPoly_rec_3 : expPolyRecCheck 3 = true := by native_decide
theorem expPoly_rec_4 : expPolyRecCheck 4 = true := by native_decide
theorem expPoly_rec_5 : expPolyRecCheck 5 = true := by native_decide
theorem expPoly_rec_6 : expPolyRecCheck 6 = true := by native_decide
theorem expPoly_rec_7 : expPolyRecCheck 7 = true := by native_decide
theorem expPoly_rec_8 : expPolyRecCheck 8 = true := by native_decide

end AnalyticContinuation
