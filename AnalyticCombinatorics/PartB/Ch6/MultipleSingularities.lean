import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace MultipleSingularities

/-!
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter VI — Contributions from Multiple Singularities

  When a generating function has several dominant singularities ζ₁,...,ζ_m
  on its circle of convergence |z| = ρ, the coefficient [zⁿ]f(z) is
  asymptotically governed by superposition of contributions from each ζⱼ.

  Key phenomena:
  • Superposition principle: [zⁿ]f(z) ~ Σⱼ contribution(ζⱼ, n)
  • Span and periodicity of coefficient sequences
  • Roots of unity filters for extracting periodic subsequences
  • Oscillatory coefficients from complex conjugate singularities
  • Daffodil lemma: span d ↔ d equally spaced dominant singularities

  Reference: Flajolet & Sedgewick, Analytic Combinatorics, Chapter VI §§4–5
-/

/-! ## 1. Periodicity and span of coefficient sequences

  The span d of f(z) = Σ aₙ zⁿ is the largest d ≥ 1 with aₙ = 0
  whenever d ∤ n. A GF of span d satisfies f(z) = g(z^d) for some
  aperiodic g, and has d equally spaced dominant singularities. -/

def hasPeriod (a : ℕ → ℚ) (d : ℕ) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    if n % d = 0 then true else decide (a n = 0)

def computeSpan (a : ℕ → ℚ) (N : ℕ) : ℕ :=
  ((List.range N).map (· + 1)).filter (hasPeriod a · N) |>.foldl max 1

def isAperiodic (a : ℕ → ℚ) (N : ℕ) : Bool :=
  computeSpan a N == 1

/-! ### Span 2: coefficients of 1/(1 − z²) = 1 + z² + z⁴ + ··· -/

def seqSpan2 : ℕ → ℚ := fun n => if n % 2 = 0 then 1 else 0

example : hasPeriod seqSpan2 2 20 = true  := by native_decide
example : hasPeriod seqSpan2 3 20 = false := by native_decide
example : computeSpan seqSpan2 20 = 2     := by native_decide

/-! ### Span 3: coefficients of 1/(1 − z³) = 1 + z³ + z⁶ + ··· -/

def seqSpan3 : ℕ → ℚ := fun n => if n % 3 = 0 then 1 else 0

example : hasPeriod seqSpan3 3 30 = true  := by native_decide
example : computeSpan seqSpan3 30 = 3     := by native_decide
example : isAperiodic seqSpan3 30 = false := by native_decide

/-! ### Aperiodic: Catalan numbers C₀=1, C₁=1, C₂=2, C₃=5, ... -/

def catalanSeq : ℕ → ℚ
  | 0 => 1 | 1 => 1 | 2 => 2 | 3 => 5 | 4 => 14
  | 5 => 42 | 6 => 132 | 7 => 429 | 8 => 1430 | _ => 0

example : isAperiodic catalanSeq 8 = true := by native_decide

/-! ## 2. Roots of unity filter

  The roots of unity filter extracts every d-th coefficient:
    (1/d) Σ_{k=0}^{d-1} f(ωᵏ z) = Σ_{n≥0} a_{dn} z^{dn}
  where ω = exp(2πi/d). For rational sequences we implement directly. -/

def extractEvery (a : ℕ → ℚ) (d : ℕ) : ℕ → ℚ :=
  fun n => a (d * n)

def evenPart (a : ℕ → ℚ) : ℕ → ℚ := fun n => a (2 * n)
def oddPart  (a : ℕ → ℚ) : ℕ → ℚ := fun n => a (2 * n + 1)

def fromBisection (e o : ℕ → ℚ) : ℕ → ℚ :=
  fun n => if n % 2 = 0 then e (n / 2) else o (n / 2)

example : evenPart catalanSeq 0 = 1  := by native_decide
example : evenPart catalanSeq 1 = 2  := by native_decide
example : evenPart catalanSeq 2 = 14 := by native_decide
example : oddPart catalanSeq 0  = 1  := by native_decide
example : oddPart catalanSeq 1  = 5  := by native_decide
example : oddPart catalanSeq 2  = 42 := by native_decide

example : fromBisection (evenPart catalanSeq) (oddPart catalanSeq) 5
        = catalanSeq 5 := by native_decide
example : fromBisection (evenPart catalanSeq) (oddPart catalanSeq) 6
        = catalanSeq 6 := by native_decide

def trisect (a : ℕ → ℚ) (r : ℕ) : ℕ → ℚ :=
  fun n => a (3 * n + r)

def fromTrisection (t0 t1 t2 : ℕ → ℚ) : ℕ → ℚ :=
  fun n => match n % 3 with
    | 0 => t0 (n / 3)
    | 1 => t1 (n / 3)
    | _ => t2 (n / 3)

example : fromTrisection (trisect catalanSeq 0) (trisect catalanSeq 1)
            (trisect catalanSeq 2) 7 = catalanSeq 7 := by native_decide
example : fromTrisection (trisect catalanSeq 0) (trisect catalanSeq 1)
            (trisect catalanSeq 2) 4 = catalanSeq 4 := by native_decide

/-! ## 3. Superposition from multiple poles

  A rational GF with denominator (1 − z/ζ₁)···(1 − z/ζ_m) has
  [zⁿ] = Σⱼ Aⱼ ζⱼ⁻ⁿ by partial fractions. For roots-of-unity
  singularities this produces periodic modulation of coefficients. -/

def poleContrib (A : ℚ) (zetaInv : ℚ) (n : ℕ) : ℚ :=
  A * zetaInv ^ n

def superpose (poles : List (ℚ × ℚ)) (n : ℕ) : ℚ :=
  poles.foldl (fun acc (A, zi) => acc + poleContrib A zi n) 0

/-! ### 1/((1−z)(1+z)) = 1/(1−z²): partial fractions (1/2)/(1−z) + (1/2)/(1+z)
  [zⁿ] = (1/2)(1 + (−1)ⁿ) -/

def twoConjugatePoles : List (ℚ × ℚ) := [(1/2, 1), (1/2, -1)]

example : superpose twoConjugatePoles 0 = 1 := by native_decide
example : superpose twoConjugatePoles 1 = 0 := by native_decide
example : superpose twoConjugatePoles 2 = 1 := by native_decide
example : superpose twoConjugatePoles 3 = 0 := by native_decide
example : superpose twoConjugatePoles 4 = 1 := by native_decide
example : superpose twoConjugatePoles 8 = 1 := by native_decide

example : superpose twoConjugatePoles 6 = seqSpan2 6 := by native_decide
example : superpose twoConjugatePoles 7 = seqSpan2 7 := by native_decide

/-! ### 1/(1−2z) − 1/(1+z): dominant pole at z=1/2 with subdominant at z=−1
  [zⁿ] = 2ⁿ − (−1)ⁿ — the (−1)ⁿ term causes small oscillation on top of 2ⁿ growth -/

def dominantSubdominant : List (ℚ × ℚ) := [(1, 2), (-1, -1)]

example : superpose dominantSubdominant 0 = 0  := by native_decide
example : superpose dominantSubdominant 1 = 3  := by native_decide
example : superpose dominantSubdominant 2 = 3  := by native_decide
example : superpose dominantSubdominant 3 = 9  := by native_decide
example : superpose dominantSubdominant 4 = 15 := by native_decide
example : superpose dominantSubdominant 5 = 33 := by native_decide

/-! ## 4. Oscillatory coefficients and sign changes

  Complex conjugate singularities produce oscillatory coefficients.
  If ζ = ρ·e^{iθ} and ζ̄ are both dominant with real GF, the combined
  contribution is 2|A|ρ⁻ⁿ cos(nθ + φ), showing periodic oscillation. -/

def signChanges (a : ℕ → ℚ) (N : ℕ) : ℕ :=
  let vals := (List.range (N + 1)).map a |>.filter (· ≠ 0)
  (vals.zip vals.tail).countP fun (x, y) => (x > 0 && y < 0) || (x < 0 && y > 0)

def positiveSeq : ℕ → ℚ := fun n => ((n + 1 : ℕ) : ℚ)

example : signChanges positiveSeq 20 = 0 := by native_decide

def alternatingSign : ℕ → ℚ := fun n => (-1 : ℚ) ^ n

example : signChanges alternatingSign 10 = 10 := by native_decide
example : signChanges alternatingSign 20 = 20 := by native_decide

def oscillationRate (a : ℕ → ℚ) (N : ℕ) : ℚ :=
  (signChanges a N : ℚ) / ((N : ℚ) + 1)

example : oscillationRate alternatingSign 9 = 9 / 10 := by native_decide
example : oscillationRate positiveSeq 20 = 0        := by native_decide

/-! ## 5. Span via GCD of support

  Equivalent characterization: span(f) = gcd{n ≥ 1 : aₙ ≠ 0}. -/

def supportGCD (a : ℕ → ℚ) (N : ℕ) : ℕ :=
  ((List.range (N + 1)).filter fun n => decide (a n ≠ 0)).foldl Nat.gcd 0

example : supportGCD seqSpan2 20 = 2 := by native_decide
example : supportGCD seqSpan3 30 = 3 := by native_decide
example : supportGCD catalanSeq 8 = 1 := by native_decide

example : computeSpan seqSpan2 20 = supportGCD seqSpan2 20 := by native_decide
example : computeSpan seqSpan3 30 = supportGCD seqSpan3 30 := by native_decide
example : computeSpan catalanSeq 8 = supportGCD catalanSeq 8 := by native_decide

/-! ## 6. Daffodil lemma and singularity theorems

  Theorem (Flajolet-Sedgewick VI.5): A GF f(z) with non-negative
  coefficients and radius ρ has span d iff its dominant singularities
  are exactly {ρ·exp(2πik/d) : k = 0,...,d−1}. -/

theorem daffodil_lemma
    (a : ℕ → ℝ) (ρ : ℝ) (d : ℕ) (hd : 0 < d) (hρ : 0 < ρ)
    (h_nonneg : ∀ n, 0 ≤ a n)
    (h_span : ∀ n, n % d ≠ 0 → a n = 0)
    (h_max : ∀ d' > d, ∃ n, n % d' ≠ 0 ∧ a n ≠ 0) :
    ∃ (sings : Finset ℂ),
      sings.card = d ∧
      ∀ ζ ∈ sings, ‖ζ‖ = ρ := by
  sorry

theorem superposition_transfer
    (coeffs : ℕ → ℝ) (contribs : ℕ → ℝ) (C : ℝ) (ρ : ℝ)
    (hC : C < 1 / ρ) (hρ : 0 < ρ) :
    (∀ᶠ n in Filter.atTop, |coeffs n - contribs n| ≤ C ^ n) →
    (∀ᶠ n in Filter.atTop, coeffs n / contribs n - 1 = 0) := by
  sorry

/-! ## 7. Motzkin numbers: aperiodic, unique dominant singularity at 1/3

  M(z) = (1 − z − √(1−2z−3z²))/(2z²) has a single dominant singularity
  at z = 1/3 (span 1), so Mₙ ~ c · 3ⁿ / n^{3/2} with no oscillation. -/

def motzkinSeq : ℕ → ℚ
  | 0 => 1 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 9
  | 5 => 21 | 6 => 51 | 7 => 127 | 8 => 323 | 9 => 835 | _ => 0

example : isAperiodic motzkinSeq 9 = true := by native_decide
example : supportGCD motzkinSeq 9 = 1     := by native_decide
example : signChanges motzkinSeq 8 = 0    := by native_decide

/-! ## 8. Asymptotic contribution from singularity type

  Near a dominant singularity ζ of type (1 − z/ζ)^{−α}, the contribution
  to [zⁿ] is ~ (ζ⁻ⁿ · n^{α−1}) / Γ(α). For multiple singularities with
  the same type, contributions add coherently or cancel by phase. -/

noncomputable def singularTypeContrib
    (zetaInv : ℂ) (alpha : ℝ) (n : ℕ) : ℂ :=
  zetaInv ^ n * (↑((n : ℝ) ^ (alpha - 1)))

noncomputable def multiSingularAsymptotics
    (contribs : List (ℂ × ℝ)) (n : ℕ) : ℂ :=
  contribs.foldl (fun acc (zi, α) => acc + singularTypeContrib zi α n) 0

theorem multi_singular_transfer
    (f : ℕ → ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (singData : List (ℂ × ℝ))
    (h_dom : ∀ p ∈ singData, ‖p.1‖ = 1 / ρ) :
    ∃ C : ℝ, 0 < C ∧ C < 1 / ρ ∧
    ∀ᶠ n in Filter.atTop,
      ‖f n - multiSingularAsymptotics singData n‖ ≤ C ^ n := by
  sorry

end MultipleSingularities
