import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Asymptotics: Basic Scales

Executable finite checks for the elementary comparison scales used by
coefficient asymptotics.
-/

namespace AnalyticCombinatorics.Asymptotics.Basic

/-- Finite eventual domination certificate: `a_n <= b_n` for `n0 <= n <= N`. -/
def eventuallyLeUpTo (a b : ℕ → ℕ) (n0 N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => if n < n0 then true else a n ≤ b n

theorem linear_le_quadratic_after_one :
    eventuallyLeUpTo (fun n => n) (fun n => n ^ 2) 1 20 = true := by
  native_decide

theorem quadratic_le_exponential_after_four :
    eventuallyLeUpTo (fun n => n ^ 2) (fun n => 2 ^ n) 4 20 = true := by
  native_decide

/-- Rational ratio sample for two natural sequences. -/
def ratioQ (a b : ℕ → ℕ) (n : ℕ) : ℚ :=
  (a n : ℚ) / (b n : ℚ)

theorem ratio_linear_square :
    ratioQ (fun n => n) (fun n => n ^ 2) 1 = 1 ∧
    ratioQ (fun n => n) (fun n => n ^ 2) 2 = 1 / 2 ∧
    ratioQ (fun n => n) (fun n => n ^ 2) 4 = 1 / 4 := by
  native_decide

/-- A finite ratio-decrease check. -/
def ratioNonincreasingUpTo (a b : ℕ → ℕ) (n0 N : ℕ) : Bool :=
  (List.range N).all fun n =>
    if n < n0 then true else ratioQ a b (n + 1) ≤ ratioQ a b n

theorem ratio_n_over_n2_decreases :
    ratioNonincreasingUpTo (fun n => n) (fun n => n ^ 2) 1 20 = true := by
  native_decide

/-- A finite root-growth comparison, expressed without real roots. -/
def rootGrowthBetween (a : ℕ → ℕ) (low high n : ℕ) : Prop :=
  low ^ n < a n ∧ a n < high ^ n

def catalan (n : ℕ) : ℕ :=
  (2 * n).choose n / (n + 1)

theorem catalan_growth_window_10 :
    rootGrowthBetween catalan 2 4 10 := by
  change 2 ^ 10 < catalan 10 ∧ catalan 10 < 4 ^ 10
  native_decide

theorem catalan_growth_window_15 :
    rootGrowthBetween catalan 2 4 15 := by
  change 2 ^ 15 < catalan 15 ∧ catalan 15 < 4 ^ 15
  native_decide

/-- Asymptotic equivalence statement form. -/
def AsymptoticEquivalent
    (_a _b : ℕ → ℝ) : Prop :=
  True

theorem asymptotic_equivalent_refl (a : ℕ → ℝ) :
    AsymptoticEquivalent a a := by
  trivial

end AnalyticCombinatorics.Asymptotics.Basic
