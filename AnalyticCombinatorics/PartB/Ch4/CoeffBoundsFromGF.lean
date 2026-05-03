import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace CoeffBoundsFromGF

/-!
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter IV — Coefficient Bounds from Generating Function Properties

  Numerical verifications and framework for:
  • Cauchy's inequality for coefficients of analytic GFs
  • Optimal radius selection in Cauchy bounds
  • Hayman's method for admissible functions
  • Coefficient bounds from singular behavior
  • Exponential upper and lower bounds via Pringsheim / Hadamard
-/

/-! ## 1. Cauchy's inequality for coefficients

  If f(z) = Σ aₙ zⁿ converges on |z| < R then
  |aₙ| ≤ M(r) / rⁿ  for any 0 < r < R,
  where M(r) = max_{|z|=r} |f(z)|.

  For f with non-negative coefficients, M(r) = f(r). -/

def cauchyBound (Mr : ℚ) (r : ℚ) (n : ℕ) : ℚ :=
  Mr / r ^ n

def geomMr (r : ℚ) : ℚ := 1 / (1 - r)

example : cauchyBound (geomMr (1/2)) (1/2) 3 = 16 := by native_decide
example : cauchyBound (geomMr (1/2)) (1/2) 5 = 64 := by native_decide
example : cauchyBound (geomMr (3/4)) (3/4) 2 = 64 / 9 := by native_decide

/-! ## 2. Optimizing the Cauchy bound

  For f(z) = 1/(1−z) the bound is B(r) = 1/((1−r) rⁿ).
  The optimal r satisfies r* = n/(n+1), yielding B(r*) = (1+1/n)ⁿ (n+1).
  As n → ∞, (1+1/n)ⁿ → e ≈ 2.718, so the bound is ~e(n+1). -/

def optimalRadius (n : ℕ) : ℚ := (n : ℚ) / ((n : ℚ) + 1)

def optimalGeomBound (n : ℕ) : ℚ :=
  cauchyBound (geomMr (optimalRadius n)) (optimalRadius n) n

example : optimalRadius 1 = 1 / 2 := by native_decide
example : optimalRadius 2 = 2 / 3 := by native_decide
example : optimalRadius 4 = 4 / 5 := by native_decide
example : optimalRadius 9 = 9 / 10 := by native_decide

-- Optimal bound at n=1: (1+1)·2 = 4
example : optimalGeomBound 1 = 4 := by native_decide
-- n=2: (3/2)² · 3 = 27/4
example : optimalGeomBound 2 = 27 / 4 := by native_decide
-- n=3: (4/3)³ · 4 = 256/27
example : optimalGeomBound 3 = 256 / 27 := by native_decide

-- The ratio optimalGeomBound(n) / (n+1) = (1+1/n)ⁿ converges to e
def almostE (n : ℕ) : ℚ :=
  if n = 0 then 1 else optimalGeomBound n / ((n : ℚ) + 1)

example : almostE 1 = 2 := by native_decide
example : almostE 2 = 9 / 4 := by native_decide
example : almostE 4 = 625 / 256 := by native_decide

-- Verify (1+1/n)ⁿ is increasing and bounded above by 3
def almostECheck (n : ℕ) : Bool :=
  if n = 0 then true else almostE n < 3 && (n < 2 || almostE (n - 1) ≤ almostE n)

example : ∀ k : Fin 15, almostECheck (k.val + 1) = true := by native_decide

/-! ## 3. Cauchy bounds for Catalan GF

  C(z) = (1 − √(1−4z))/(2z), radius R = 1/4.
  Coefficients Cₙ = C(2n,n)/(n+1). Cauchy bound at r:
  B(r) = C(r) / rⁿ. -/

def catalanNumber (n : ℕ) : ℕ :=
  match n with
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 5
  | 4 => 14
  | 5 => 42
  | 6 => 132
  | 7 => 429
  | 8 => 1430
  | 9 => 4862
  | 10 => 16796
  | 11 => 58786
  | _ => 0

def catalanBoundRatio (r_num r_den : ℕ) (n : ℕ) : ℚ :=
  let r : ℚ := (r_num : ℚ) / (r_den : ℚ)
  (catalanNumber n : ℚ) * r ^ n

example : catalanBoundRatio 1 5 0 = 1 := by native_decide
example : catalanBoundRatio 1 5 1 = 1 / 5 := by native_decide
example : catalanBoundRatio 1 5 3 = 1 / 25 := by native_decide
example : catalanBoundRatio 1 5 5 = 42 / 3125 := by native_decide

example : catalanBoundRatio 1 4 4 = 14 / 256 := by native_decide
example : catalanBoundRatio 1 4 6 = 132 / 4096 := by native_decide

/-! ## 4. Exponential growth rates and bounds

  For a sequence aₙ with radius R, exponential growth ρ = 1/R.
  aₙ ≤ C · ρⁿ for some constant C (upper bound).
  If aₙ ≥ 0 and R is a singularity (Pringsheim), aₙ ≥ c · ρⁿ / p(n)
  for some polynomial p and constant c > 0 (effective lower bound). -/

structure ExpBound where
  family : String
  radius_inv : ℚ
  subexp_factor : String
  deriving DecidableEq, Repr

def catalanExpBound : ExpBound :=
  { family := "Catalan"
    radius_inv := 4
    subexp_factor := "n^(-3/2) / sqrt(pi)" }

def motzkinExpBound : ExpBound :=
  { family := "Motzkin"
    radius_inv := 3
    subexp_factor := "c · n^(-3/2)" }

def bellExpBound : ExpBound :=
  { family := "Bell (EGF radius 0)"
    radius_inv := 0
    subexp_factor := "super-exponential: B_n / n! has radius ∞" }

example : catalanExpBound.radius_inv = 4 := by native_decide
example : motzkinExpBound.radius_inv = 3 := by native_decide

-- Verify Catalan numbers satisfy Cₙ ≤ 4ⁿ for small n
def catalanUpperBoundCheck (n : ℕ) : Bool := catalanNumber n ≤ 4 ^ n

example : ∀ k : Fin 12, catalanUpperBoundCheck k.val = true := by native_decide

-- Verify Catalan numbers satisfy Cₙ ≥ 2ⁿ for n ≥ 5 (exponential lower bound)
def catalanLowerBoundCheck (n : ℕ) : Bool := n < 5 || catalanNumber n ≥ 2 ^ n

example : ∀ k : Fin 12, catalanLowerBoundCheck k.val = true := by native_decide

/-! ## 5. Hayman admissibility framework

  A function f(z) = Σ aₙ zⁿ is H-admissible if the saddle-point
  method applies. Key quantities:
  a(r) = r f'(r)/f(r)   (mean index)
  b(r) = r a'(r)         (variance)
  Then aₙ ≈ f(rₙ) / (rₙⁿ √(2π b(rₙ))) where a(rₙ) = n. -/

structure HaymanData where
  family : String
  meanFunction : String
  varianceFunction : String
  saddlePointEq : String
  asymptoticForm : String
  deriving DecidableEq, Repr

def expHayman : HaymanData :=
  { family := "exp(z)"
    meanFunction := "a(r) = r"
    varianceFunction := "b(r) = r"
    saddlePointEq := "r_n = n"
    asymptoticForm := "1/n! ~ e^n / (n^n sqrt(2 pi n))" }

def exp2Hayman : HaymanData :=
  { family := "exp(z + z²/2)"
    meanFunction := "a(r) = r + r²"
    varianceFunction := "b(r) = r + 2r²"
    saddlePointEq := "r_n + r_n² = n"
    asymptoticForm := "set partitions: approximate saddle-point" }

example : expHayman.family = "exp(z)" := by native_decide

-- Verify factorial growth: n! ≤ nⁿ for n ≥ 1
def factUpperCheck (n : ℕ) : Bool := n = 0 || Nat.factorial n ≤ n ^ n

example : ∀ k : Fin 10, factUpperCheck k.val = true := by native_decide

/-! ## 6. Coefficient ratios and exponential type

  For meromorphic GFs, aₙ₊₁/aₙ → 1/R.
  Deviations from this limit encode sub-exponential factors. -/

def coeffRatio (a : ℕ → ℕ) (n : ℕ) : ℚ :=
  if a n = 0 then 0 else (a (n + 1) : ℚ) / (a n : ℚ)

-- Catalan: Cₙ₊₁/Cₙ → 4
example : coeffRatio catalanNumber 3  = 14 / 5     := by native_decide
example : coeffRatio catalanNumber 5  = 132 / 42   := by native_decide
example : coeffRatio catalanNumber 7  = 1430 / 429 := by native_decide
example : coeffRatio catalanNumber 9  = 16796 / 4862 := by native_decide

-- Ratio approaches 4 from below: verify ratio < 4 for small n
def catalanRatioBelow4 (n : ℕ) : Bool :=
  n = 0 || coeffRatio catalanNumber n < 4

example : ∀ k : Fin 11, catalanRatioBelow4 k.val = true := by native_decide

-- Geometric: aₙ = 2ⁿ, ratio = 2 exactly
def geomSeq (n : ℕ) : ℕ := 2 ^ n

example : ∀ k : Fin 10, coeffRatio geomSeq k.val = 2 := by native_decide

/-! ## 7. Summary: bounds hierarchy

  Weakest to strongest coefficient information:
  1. Exponential type: aₙ = O(ρⁿ) for ρ = 1/R
  2. Cauchy bound at optimal r: aₙ ≤ f(r*)/r*ⁿ
  3. Hayman / saddle-point: aₙ ~ f(rₙ)/(rₙⁿ √(2πb(rₙ)))
  4. Transfer theorem: aₙ ~ C ρⁿ n^α (exact asymptotics) -/

inductive BoundStrength where
  | exponentialType
  | cauchyOptimal
  | haymanSaddlePoint
  | singularityTransfer
  deriving DecidableEq, Repr

def boundStrengthOrder : BoundStrength → ℕ
  | BoundStrength.exponentialType => 1
  | BoundStrength.cauchyOptimal => 2
  | BoundStrength.haymanSaddlePoint => 3
  | BoundStrength.singularityTransfer => 4

theorem transfer_strongest :
    boundStrengthOrder BoundStrength.singularityTransfer =
    4 := by native_decide

theorem exponential_weakest :
    ∀ b : BoundStrength,
      boundStrengthOrder BoundStrength.exponentialType ≤
      boundStrengthOrder b := by
  intro b; cases b <;> native_decide

theorem bound_ordering :
    boundStrengthOrder BoundStrength.exponentialType <
    boundStrengthOrder BoundStrength.cauchyOptimal ∧
    boundStrengthOrder BoundStrength.cauchyOptimal <
    boundStrengthOrder BoundStrength.haymanSaddlePoint ∧
    boundStrengthOrder BoundStrength.haymanSaddlePoint <
    boundStrengthOrder BoundStrength.singularityTransfer := by
  constructor <;> [native_decide; constructor <;> native_decide]

end CoeffBoundsFromGF
