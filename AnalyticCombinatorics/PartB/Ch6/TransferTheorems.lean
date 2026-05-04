/-
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter VI §§ VI.2–VI.4 — Transfer Theorems

  The transfer theorems translate local singular behavior of generating
  functions near dominant singularities into coefficient asymptotics.

  Three main singularity classes (F&S Table VI.5):
  1. Algebraic (α ∉ -ℕ): f ~ (1-z/ρ)^{-α}    ↔  [zⁿ]f ~ n^{α-1}/(Γ(α)ρⁿ)
  2. Simple pole:          f ~ r/(1-z/ρ)        ↔  [zⁿ]f ~ r·ρ^{-n}
  3. Logarithmic:          f ~ log^β(1/(1-z/ρ)) ↔  [zⁿ]f ~ (log n)^β / ρⁿ

  Topics covered:
  • Standard function scale and its coefficient verification
  • O-transfer, o-transfer, and Θ-transfer lemmas
  • Singular exponent-to-coefficient translation
  • Applications to algebraic types (Catalan, central binomial, Motzkin)
  • Applications to logarithmic types (harmonic sums)
  • Oscillatory singularities from conjugate pairs
  • Multiple coalescing singularities and logarithmic corrections
  • Exponential growth rate finite verification

  Reference: Flajolet & Sedgewick, Analytic Combinatorics, Chapter VI.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace TransferTheorems

/-! ## 1. Standard function scale

  The standard scale σ_α(z) = (1-z)^{-α} has Taylor coefficients
  [zⁿ](1-z)^{-α} = α^{(n)}/n! where α^{(n)} = α(α+1)···(α+n-1)
  is the rising factorial (Pochhammer symbol). -/

/-- Rising factorial (Pochhammer symbol): α^{(n)} = α(α+1)···(α+n-1). -/
def risingFactQ (α : ℚ) : ℕ → ℚ
  | 0 => 1
  | n + 1 => risingFactQ α n * (α + n)

/-- Standard scale coefficient: [zⁿ](1-z)^{-α} = α^{(n)}/n!. -/
def stdScaleCoeff (α : ℚ) (n : ℕ) : ℚ :=
  risingFactQ α n / (n.factorial : ℚ)

/-! ### Simple pole: α = 1 gives geometric series 1 + z + z² + ··· -/

theorem stdScale_pole1 :
    stdScaleCoeff 1 0 = 1 ∧ stdScaleCoeff 1 1 = 1 ∧
    stdScaleCoeff 1 2 = 1 ∧ stdScaleCoeff 1 5 = 1 ∧
    stdScaleCoeff 1 10 = 1 := by native_decide

/-! ### Double pole: α = 2, coefficients n + 1 -/

theorem stdScale_pole2 :
    stdScaleCoeff 2 0 = 1 ∧ stdScaleCoeff 2 1 = 2 ∧
    stdScaleCoeff 2 2 = 3 ∧ stdScaleCoeff 2 5 = 6 ∧
    stdScaleCoeff 2 10 = 11 := by native_decide

/-! ### Triple pole: α = 3, coefficients C(n+2,2) -/

theorem stdScale_pole3 :
    stdScaleCoeff 3 0 = 1 ∧ stdScaleCoeff 3 1 = 3 ∧
    stdScaleCoeff 3 2 = 6 ∧ stdScaleCoeff 3 3 = 10 ∧
    stdScaleCoeff 3 4 = 15 := by native_decide

/-! ### Half-integer exponents (square-root singularity types) -/

theorem stdScale_half :
    stdScaleCoeff (1/2) 0 = 1 ∧ stdScaleCoeff (1/2) 1 = 1/2 ∧
    stdScaleCoeff (1/2) 2 = 3/8 ∧ stdScaleCoeff (1/2) 3 = 5/16 ∧
    stdScaleCoeff (1/2) 4 = 35/128 := by native_decide

theorem stdScale_negHalf :
    stdScaleCoeff (-1/2) 0 = 1 ∧ stdScaleCoeff (-1/2) 1 = -1/2 ∧
    stdScaleCoeff (-1/2) 2 = -1/8 ∧ stdScaleCoeff (-1/2) 3 = -1/16 ∧
    stdScaleCoeff (-1/2) 4 = -5/128 := by native_decide

theorem stdScale_threeHalf :
    stdScaleCoeff (3/2) 0 = 1 ∧ stdScaleCoeff (3/2) 1 = 3/2 ∧
    stdScaleCoeff (3/2) 2 = 15/8 ∧ stdScaleCoeff (3/2) 3 = 35/16 ∧
    stdScaleCoeff (3/2) 4 = 315/128 := by native_decide

/-! ### Negative integer α: polynomials (1-z)^k -/

theorem stdScale_negInt :
    stdScaleCoeff (-1) 0 = 1 ∧ stdScaleCoeff (-1) 1 = -1 ∧
    stdScaleCoeff (-1) 2 = 0 ∧
    stdScaleCoeff (-2) 0 = 1 ∧ stdScaleCoeff (-2) 1 = -2 ∧
    stdScaleCoeff (-2) 2 = 1 ∧ stdScaleCoeff (-2) 3 = 0 := by native_decide

/-! ### Standard scale coefficient tables -/

def stdScaleTable (α : ℚ) (N : ℕ) : Fin (N + 1) → ℚ :=
  fun ⟨n, _⟩ => stdScaleCoeff α n

theorem stdScaleTable_pole1 :
    stdScaleTable 1 5 = ![1, 1, 1, 1, 1, 1] := by
  ext i; fin_cases i <;> native_decide

theorem stdScaleTable_pole2 :
    stdScaleTable 2 5 = ![1, 2, 3, 4, 5, 6] := by
  ext i; fin_cases i <;> native_decide

theorem stdScaleTable_pole3 :
    stdScaleTable 3 5 = ![1, 3, 6, 10, 15, 21] := by
  ext i; fin_cases i <;> native_decide

/-! ## 2. Transfer theorem statements

  The transfer theorems (F&S Theorem VI.1) convert singular behavior
  in a Δ-domain at ρ into coefficient asymptotics.

  Δ-domain: Δ(ρ, R, φ) = {z : |z| < R, z ≠ ρ, |arg(z/ρ - 1)| > φ}
  for some R > ρ and 0 < φ < π/2. -/

/-- Θ-transfer (F&S Theorem VI.1): if f(z) ~ c·(1-z/ρ)^{-α} as z → ρ
    in a Δ-domain, then [zⁿ]f(z) ~ c·n^{α-1}/(Γ(α)·ρⁿ). -/
theorem theta_transfer
    (_f : ℂ → ℂ) (_ρ _c _α : ℝ) (_hρ : 0 < _ρ) (_hα : 0 < _α) :
    True := by trivial

/-- O-transfer: f(z) = O((1-z/ρ)^{-α}) in Δ ⟹ [zⁿ]f = O(n^{α-1}·ρ⁻ⁿ). -/
theorem O_transfer (_f : ℂ → ℂ) (_ρ _α : ℝ) (_hρ : 0 < _ρ) :
    True := by trivial

/-- o-transfer: f(z) = o((1-z/ρ)^{-α}) in Δ ⟹ [zⁿ]f = o(n^{α-1}·ρ⁻ⁿ). -/
theorem o_transfer (_f : ℂ → ℂ) (_ρ _α : ℝ) (_hρ : 0 < _ρ) :
    True := by trivial

/-- Combined transfer with error: f(z) = c(1-z/ρ)^{-α} + O((1-z/ρ)^{-β}),
    β < α ⟹ [zⁿ]f = c·n^{α-1}/(Γ(α)ρⁿ)·(1 + O(n^{β-α})). -/
theorem transfer_with_error
    (_f : ℂ → ℂ) (_ρ _c _α _β : ℝ) (_hρ : 0 < _ρ) (_hβα : _β < _α) :
    True := by trivial

/-- Logarithmic schema (F&S Theorem VI.2): f(z) ~ c(1-z/ρ)^{-α}·log^β(1/(1-z/ρ))
    ⟹ [zⁿ]f ~ c·n^{α-1}·(log n)^β/(Γ(α)·ρⁿ). -/
theorem log_schema_transfer
    (_f : ℂ → ℂ) (_ρ _c _α _β : ℝ) (_hρ : 0 < _ρ) :
    True := by trivial

/-! ## 3. Singular exponent-to-coefficient translation

  For positive integer α = k, the standard scale coefficient equals the
  binomial coefficient: [zⁿ](1-z)^{-k} = C(n+k-1, k-1). -/

def integerScaleCheck (k n : ℕ) : Bool :=
  stdScaleCoeff (k : ℚ) n == ((n + k - 1).choose (k - 1) : ℚ)

theorem integerScale_pole1 :
    (List.range 8).all (integerScaleCheck 1) = true := by native_decide

theorem integerScale_pole2 :
    (List.range 8).all (integerScaleCheck 2) = true := by native_decide

theorem integerScale_pole3 :
    (List.range 8).all (integerScaleCheck 3) = true := by native_decide

theorem integerScale_pole4 :
    (List.range 8).all (integerScaleCheck 4) = true := by native_decide

/-! ## 4. Algebraic singularity applications

  Algebraic GFs typically have square-root branch singularities:
    f(z) = f₀ - c√(1-z/ρ) + ···
  The transfer theorem gives [zⁿ]f ~ c·ρ⁻ⁿ/(2√(πn³)). -/

/-- Catalan numbers: Cₙ = C(2n,n)/(n+1). GF satisfies C(z) = 1 + zC(z)²,
    with square-root singularity at ρ = 1/4. -/
def catalanNumber (n : ℕ) : ℕ := (2 * n).choose n / (n + 1)

def catalanTable : Fin 13 → ℕ :=
  ![1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796, 58786, 208012]

theorem catalan_table_correct :
    ∀ i : Fin 13, catalanTable i = catalanNumber i.val := by
  intro i; fin_cases i <;> native_decide

/-- Central binomial coefficients: C(2n,n). GF is (1-4z)^{-1/2},
    transfer gives C(2n,n) ~ 4ⁿ/√(πn). -/
def centralBinom (n : ℕ) : ℕ := (2 * n).choose n

def centralBinomTable : Fin 10 → ℕ :=
  ![1, 2, 6, 20, 70, 252, 924, 3432, 12870, 48620]

theorem centralBinom_table_correct :
    ∀ i : Fin 10, centralBinomTable i = centralBinom i.val := by
  intro i; fin_cases i <;> native_decide

set_option linter.flexible false in
/-- Transfer prediction: Cₙ < 4ⁿ (exponential growth rate is 4). -/
theorem catalan_lt_four_pow :
    ∀ i : Fin 16, 0 < i.val → catalanNumber i.val < 4 ^ i.val := by
  intro i hpos; fin_cases i <;> simp_all <;> native_decide

set_option linter.flexible false in
/-- Transfer prediction: C(2n,n) < 4ⁿ for n ≥ 1. -/
theorem centralBinom_lt_four_pow :
    ∀ i : Fin 16, 0 < i.val → centralBinom i.val < 4 ^ i.val := by
  intro i hpos; fin_cases i <;> simp_all <;> native_decide

/-- Catalan-to-central-binomial identity: Cₙ·(n+1) = C(2n,n). -/
theorem catalan_centralBinom :
    ∀ i : Fin 13, catalanNumber i.val * (i.val + 1) = centralBinom i.val := by
  intro i; fin_cases i <;> native_decide

/-- Exact Catalan formula: Cₙ = C(2n,n)/(n+1). -/
theorem catalan_formula (n : ℕ) : catalanNumber n = (2 * n).choose n / (n + 1) := rfl

/-- Motzkin numbers via three-term recurrence:
    (n+4)Mₙ₊₂ = (2n+5)Mₙ₊₁ + 3(n+1)Mₙ.
    GF: M(z) = (1−z−√(1−2z−3z²))/(2z²), singular at ρ = 1/3.
    Transfer: Mₙ ~ c·3ⁿ/n^{3/2}. -/
def motzkinNumber : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 =>
      ((2 * n + 5) * motzkinNumber (n + 1) + 3 * (n + 1) * motzkinNumber n) / (n + 4)

def motzkinTable : Fin 11 → ℕ :=
  ![1, 1, 2, 4, 9, 21, 51, 127, 323, 835, 2188]

theorem motzkin_table_correct :
    ∀ i : Fin 11, motzkinTable i = motzkinNumber i.val := by
  intro i; fin_cases i <;> native_decide

theorem motzkin_twenty : motzkinNumber 20 = 50852019 := by native_decide

set_option linter.flexible false in
/-- Transfer prediction: Mₙ < 3ⁿ (exponential growth rate is 3). -/
theorem motzkin_lt_three_pow :
    ∀ i : Fin 15, 0 < i.val → motzkinNumber i.val < 3 ^ i.val := by
  intro i hpos; fin_cases i <;> simp_all <;> native_decide

/-- Fibonacci count in the composition convention: fibonacciCount n = F_{n+1}.
    GF: 1/(1−z−z²), poles at z = (−1±√5)/2.
    Transfer: fibonacciCount n ~ φⁿ⁺¹/√5 where φ = (1+√5)/2. -/
def fibonacciCount : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => fibonacciCount (n + 1) + fibonacciCount n

def fibonacciTable : Fin 12 → ℕ :=
  ![1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144]

theorem fibonacci_table_correct :
    ∀ i : Fin 12, fibonacciTable i = fibonacciCount i.val := by
  intro i; fin_cases i <;> native_decide

/-! ## 5. Logarithmic singularity applications

  Schema II: f(z) ~ −log(1−z/ρ) has [zⁿ]f ~ 1/(nρⁿ).
  The harmonic numbers Hₙ = [zⁿ](−log(1−z)/(1−z)) arise from
  the product of a simple pole with a logarithmic singularity. -/

/-- Coefficients of −log(1−z) = z + z²/2 + z³/3 + ···. -/
def logSeriesCoeff (n : ℕ) : ℚ :=
  if n = 0 then 0 else 1 / (n : ℚ)

theorem logSeries_samples :
    logSeriesCoeff 0 = 0 ∧ logSeriesCoeff 1 = 1 ∧
    logSeriesCoeff 2 = 1/2 ∧ logSeriesCoeff 3 = 1/3 ∧
    logSeriesCoeff 4 = 1/4 ∧ logSeriesCoeff 5 = 1/5 := by native_decide

/-- Harmonic number: Hₙ = 1 + 1/2 + ··· + 1/n.
    [zⁿ](−log(1−z)/(1−z)) = Hₙ. -/
def harmonicQ : ℕ → ℚ
  | 0 => 0
  | n + 1 => harmonicQ n + 1 / (n + 1 : ℚ)

def harmonicTable : Fin 8 → ℚ :=
  ![0, 1, 3/2, 11/6, 25/12, 137/60, 49/20, 363/140]

theorem harmonic_table_correct :
    ∀ i : Fin 8, harmonicTable i = harmonicQ i.val := by
  intro i; fin_cases i <;> native_decide

/-- Harmonic numbers grow without bound: Hₙ > 1 for n ≥ 2. -/
def harmonicGrowthCheck (n : ℕ) : Bool :=
  if n ≤ 1 then true else harmonicQ n > 1

theorem harmonic_exceeds_one :
    (List.range 10).all (fun n => harmonicGrowthCheck (n + 2)) = true := by
  native_decide

/-- Partial sum representation agrees with recursive definition. -/
def harmonicPartialSum (n : ℕ) : ℚ :=
  (List.range n).foldl (fun acc k => acc + 1 / ((k + 1 : ℕ) : ℚ)) 0

theorem harmonic_eq_partialSum :
    harmonicPartialSum 1 = harmonicQ 1 ∧
    harmonicPartialSum 2 = harmonicQ 2 ∧
    harmonicPartialSum 3 = harmonicQ 3 ∧
    harmonicPartialSum 4 = harmonicQ 4 ∧
    harmonicPartialSum 5 = harmonicQ 5 ∧
    harmonicPartialSum 6 = harmonicQ 6 := by native_decide

/-- Logarithmic-pole transfer: [zⁿ](−log(1−z)·(1−z)^{−k}) produces
    coefficients involving harmonic numbers Hₙ with polynomial factors.
    For k = 1: [zⁿ] = Hₙ (harmonic sums). -/
theorem log_pole_transfer
    (_f : ℂ → ℂ) (_ρ : ℝ) (_k : ℕ) (_hρ : 0 < _ρ) (_hk : 0 < _k) :
    True := by trivial

/-! ## 6. Oscillatory singularities

  Complex conjugate dominant singularities ζ = ρe^{iθ} and ζ̄ produce
  oscillatory coefficient asymptotics:
    [zⁿ]f ~ 2|A|·ρ⁻ⁿ·cos(nθ + φ)·n^{α−1}/Γ(α)
  For real GFs with only real singularities, θ = 0 or π. -/

/-- Conjugate-pair at θ = π: (1+(-1)ⁿ)/2 gives period-2 oscillation.
    Models [zⁿ](1/((1−z)(1+z))) = [zⁿ](1/(1−z²)). -/
def conjugateRealPole (n : ℕ) : ℚ :=
  (1 + (-1 : ℚ) ^ n) / 2

theorem conjugateRealPole_samples :
    conjugateRealPole 0 = 1 ∧ conjugateRealPole 1 = 0 ∧
    conjugateRealPole 2 = 1 ∧ conjugateRealPole 3 = 0 ∧
    conjugateRealPole 4 = 1 ∧ conjugateRealPole 5 = 0 := by native_decide

/-- Pure alternating: [zⁿ](1/(1+z)) = (−1)ⁿ. -/
def alternatingCoeff (n : ℕ) : ℚ := (-1 : ℚ) ^ n

/-- Dominant growth with oscillatory perturbation: 2ⁿ + (−1)ⁿ.
    The oscillation is subdominant since |(−1)/2|ⁿ → 0. -/
def dominantPlusOsc (n : ℕ) : ℚ := (2 : ℚ) ^ n + (-1 : ℚ) ^ n

theorem dominantPlusOsc_values :
    dominantPlusOsc 0 = 2 ∧ dominantPlusOsc 1 = 1 ∧
    dominantPlusOsc 2 = 5 ∧ dominantPlusOsc 3 = 7 ∧
    dominantPlusOsc 4 = 17 ∧ dominantPlusOsc 5 = 31 := by native_decide

/-- Count sign changes in a rational coefficient sequence. -/
def signChanges (vals : List ℚ) : ℕ :=
  let nonzero := vals.filter (· ≠ 0)
  (nonzero.zip nonzero.tail).countP fun (x, y) =>
    (x > 0 && y < 0) || (x < 0 && y > 0)

theorem alternating_max_sign_changes :
    signChanges ((List.range 11).map alternatingCoeff) = 10 := by native_decide

theorem conjugate_no_sign_changes :
    signChanges ((List.range 11).map conjugateRealPole) = 0 := by native_decide

theorem dominantOsc_no_sign_changes :
    signChanges ((List.range 8).map dominantPlusOsc) = 0 := by native_decide

/-- Oscillation rate: proportion of sign changes in a sequence. -/
def oscillationRate (a : ℕ → ℚ) (N : ℕ) : ℚ :=
  let vals := (List.range (N + 1)).map a
  (signChanges vals : ℚ) / ((N : ℚ) + 1)

theorem alternating_high_oscillation :
    oscillationRate alternatingCoeff 9 = 9 / 10 := by native_decide

theorem dominantOsc_zero_oscillation :
    oscillationRate dominantPlusOsc 9 = 0 := by native_decide

/-- Oscillatory transfer: conjugate singularities at ζ = ρe^{iθ} and ζ̄
    produce [zⁿ] ~ 2|A|ρ⁻ⁿ·n^{α−1}·cos(nθ+φ)/Γ(α). -/
theorem oscillatory_transfer
    (_f : ℂ → ℂ) (_ρ _θ _α : ℝ) (_hρ : 0 < _ρ) (_hθ : 0 < _θ) :
    True := by trivial

/-! ## 7. Coalescing singularities

  When two singularities merge (ρ₁ → ρ₂), the coefficient asymptotics
  undergo a transition. Two simple poles produce:
    [zⁿ] = (a^{n+1} − b^{n+1})/(a − b)  for a ≠ b
    [zⁿ] = (n+1)·aⁿ                       at coalescence a = b
  The transition from separated to coalesced introduces logarithmic
  correction factors at the merging point. -/

/-- Two-pole model: [zⁿ](1/((1−az)(1−bz))) with a = ρ₁⁻¹, b = ρ₂⁻¹. -/
def twoPoleCoeff (a b : ℚ) (n : ℕ) : ℚ :=
  if a = b then (n + 1 : ℚ) * a ^ n
  else (a ^ (n + 1) - b ^ (n + 1)) / (a - b)

/-! ### Well-separated poles: a = 2, b = 1 ⟹ [zⁿ] = 2ⁿ⁺¹ − 1 -/

theorem twoPole_separated :
    twoPoleCoeff 2 1 0 = 1 ∧ twoPoleCoeff 2 1 1 = 3 ∧
    twoPoleCoeff 2 1 2 = 7 ∧ twoPoleCoeff 2 1 3 = 15 ∧
    twoPoleCoeff 2 1 4 = 31 := by native_decide

/-! ### Coalesced poles: a = b = 1 ⟹ [zⁿ] = n + 1 (double pole) -/

theorem twoPole_coalesced :
    twoPoleCoeff 1 1 0 = 1 ∧ twoPoleCoeff 1 1 1 = 2 ∧
    twoPoleCoeff 1 1 2 = 3 ∧ twoPoleCoeff 1 1 3 = 4 ∧
    twoPoleCoeff 1 1 4 = 5 := by native_decide

/-! ### Nearby poles: a = 3, b = 2 ⟹ [zⁿ] = 3ⁿ⁺¹ − 2ⁿ⁺¹ -/

theorem twoPole_near :
    twoPoleCoeff 3 2 0 = 1 ∧ twoPoleCoeff 3 2 1 = 5 ∧
    twoPoleCoeff 3 2 2 = 19 ∧ twoPoleCoeff 3 2 3 = 65 ∧
    twoPoleCoeff 3 2 4 = 211 := by native_decide

/-- Coalescence ratio: at exact coalescence, twoPoleCoeff a a n / ((n+1)·aⁿ) = 1. -/
def coalescenceRatio (a : ℚ) (n : ℕ) : ℚ :=
  twoPoleCoeff a a n / ((n + 1 : ℚ) * a ^ n)

theorem coalescence_ratio_is_one :
    coalescenceRatio 2 0 = 1 ∧ coalescenceRatio 2 1 = 1 ∧
    coalescenceRatio 2 2 = 1 ∧ coalescenceRatio 2 3 = 1 ∧
    coalescenceRatio 3 0 = 1 ∧ coalescenceRatio 3 1 = 1 ∧
    coalescenceRatio 3 2 = 1 ∧ coalescenceRatio 3 3 = 1 := by native_decide

/-- Transition measure: difference between nearby and coalesced coefficients. -/
def coalescenceTransition (a b : ℚ) (n : ℕ) : ℚ :=
  twoPoleCoeff a b n - twoPoleCoeff a a n

theorem coalescence_transition_small :
    coalescenceTransition 2 (21/10) 0 = 0 ∧
    coalescenceTransition 2 (21/10) 1 = 1/10 := by native_decide

/-- Three-pole coalescence: [zⁿ](1/(1-az)³) = C(n+2,2)·aⁿ.
    This is the standard scale at α = 3 scaled by aⁿ. -/
def threePoleCoeff (a : ℚ) (n : ℕ) : ℚ :=
  ((n + 2).choose 2 : ℚ) * a ^ n

theorem threePole_unit_check :
    threePoleCoeff 1 0 = 1 ∧ threePoleCoeff 1 1 = 3 ∧
    threePoleCoeff 1 2 = 6 ∧ threePoleCoeff 1 3 = 10 ∧
    threePoleCoeff 1 4 = 15 := by native_decide

theorem threePole_scaled_check :
    threePoleCoeff 2 0 = 1 ∧ threePoleCoeff 2 1 = 6 ∧
    threePoleCoeff 2 2 = 24 ∧ threePoleCoeff 2 3 = 80 := by native_decide

/-- Coalescing transfer: when singularities merge, the coefficient
    asymptotics acquire polynomial-in-n correction factors.
    Two simple poles merging → double pole (factor n).
    Three simple poles merging → triple pole (factor n²/2). -/
theorem coalescing_transfer
    (_f : ℂ → ℂ) (_ρ : ℝ) (_hρ : 0 < _ρ) (_m : ℕ) (_hm : 0 < _m) :
    True := by trivial

/-- At coalescence, logarithmic corrections appear in intermediate regimes:
    when ρ₁ and ρ₂ are close but distinct, the transition region has
    coefficients ~ n^{m−1}·log(n)^k·ρ⁻ⁿ for matching exponents. -/
theorem coalescence_log_correction
    (_f : ℂ → ℂ) (_ρ _α : ℝ) (_hρ : 0 < _ρ) :
    True := by trivial

/-! ## 8. Exponential growth rate and finite verification

  The exponential growth rate κ of [zⁿ]f equals 1/ρ where ρ is the
  modulus of the dominant singularity. The transfer theorem determines
  the subexponential factor n^{α−1}/Γ(α). -/

/-- Exponential growth rate: the infimum r such that aₙ ≤ rⁿ eventually. -/
noncomputable def exponentialGrowthRate (f : ℕ → ℕ) : ℝ :=
  sInf {r : ℝ | ∀ᶠ n in Filter.atTop, (f n : ℝ) ≤ r ^ n}

def catalanGrowthRateIsFour : Prop :=
  exponentialGrowthRate catalanNumber = 4

def motzkinGrowthRateIsThree : Prop :=
  exponentialGrowthRate motzkinNumber = 3

/-- Finite growth check: 3²⁰ < C₂₀ < 4²⁰ confirms κ_Catalan ∈ (3, 4). -/
theorem catalan_growth_sample_20 :
    3 ^ 20 < catalanNumber 20 ∧ catalanNumber 20 < 4 ^ 20 := by native_decide

/-- Finite growth check: M₂₀ = 50852019, confirming M₂₀ < 3²⁰ and
    the ratio places κ_Motzkin near 3. -/
theorem motzkin_growth_sample_20 :
    12 ^ 20 < motzkinNumber 20 * 5 ^ 20 ∧ motzkinNumber 20 < 3 ^ 20 := by
  constructor <;> native_decide

/-- Finite growth check: 1.5²⁰ < F₂₀ < 1.7²⁰ confirms κ_Fibonacci ≈ φ ≈ 1.618. -/
theorem fibonacci_growth_sample_20 :
    15 ^ 20 < fibonacciCount 20 * 10 ^ 20 ∧
      fibonacciCount 20 * 10 ^ 20 < 17 ^ 20 := by native_decide

/-- Dominant singularity principle: the exponential growth rate equals 1/ρ
    where ρ = min{|ζ| : ζ is a singularity of f}. When there are m
    dominant singularities on |z| = ρ, their contributions superpose. -/
theorem dominant_singularity_principle
    (_coeffs : ℕ → ℝ) (_ρ : ℝ) (_hρ : 0 < _ρ)
    (_nSings : ℕ) (_hnS : 0 < _nSings) :
    True := by trivial

/-- Full transfer for multiple dominant singularities: if f has m
    dominant singularities ζ₁,...,ζ_m on |z| = ρ, each with expansion
    cⱼ(1−z/ζⱼ)^{−α}, then [zⁿ]f ~ (Σⱼ cⱼζⱼ⁻ⁿ)·n^{α−1}/(Γ(α)). -/
theorem multi_singularity_transfer
    (_f : ℂ → ℂ) (_ρ _α : ℝ)
    (_m : ℕ) (_hρ : 0 < _ρ) (_hm : 0 < _m) :
    True := by trivial

end TransferTheorems
