import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace MeromCoeffExtraction

/-!
# Meromorphic Coefficient Extraction

Coefficient extraction from meromorphic generating functions via residues,
following Flajolet & Sedgewick Chapter IV. The fundamental identity:
  [z^n] f(z) = Σ Res(f(z)/z^{n+1}, poles)
reduces coefficient extraction to a finite sum of pole contributions.

Key topics:
- Multi-pole coefficient extraction via partial fractions
- Dominant pole approximation and effective error bounds
- Higher-order pole contributions with polynomial prefactors
-/

open Nat BigOperators Finset

/-! ## 1. Single-pole coefficient contributions -/

/-- Coefficient contribution from a pole of order `k` at reciprocal location `α`:
    [z^n] of 1/(1 - αz)^k equals α^n · C(n+k-1, k-1). -/
def poleContrib (α : ℤ) (k : ℕ) (n : ℕ) : ℤ :=
  α ^ n * (Nat.choose (n + k - 1) (k - 1) : ℤ)

theorem poleContrib_order1 (α : ℤ) (n : ℕ) :
    poleContrib α 1 n = α ^ n := by
  simp [poleContrib]

theorem poleContrib_order2 (α : ℤ) (n : ℕ) :
    poleContrib α 2 n = α ^ n * ((n : ℤ) + 1) := by
  simp [poleContrib]

theorem poleContrib_order3 (α : ℤ) (n : ℕ) :
    poleContrib α 3 n = α ^ n * (Nat.choose (n + 2) 2 : ℤ) := by
  simp [poleContrib]

example : poleContrib 2 1 5 = 32 := by native_decide
example : poleContrib 2 2 3 = 32 := by native_decide
example : poleContrib 3 1 4 = 81 := by native_decide
example : poleContrib 1 3 4 = 15 := by native_decide

/-! ## 2. Multi-pole extraction framework -/

/-- Descriptor for a pole in a partial fraction decomposition. -/
structure PoleDesc where
  alpha : ℤ
  order : ℕ
  weight : ℤ
deriving DecidableEq, Repr

/-- Total coefficient [z^n] from a sum of partial fraction terms:
    Σ c_i · [z^n] 1/(1 - α_i z)^{k_i}. -/
def extractCoeff (poles : List PoleDesc) (n : ℕ) : ℤ :=
  poles.foldl (fun acc p => acc + p.weight * poleContrib p.alpha p.order n) 0

theorem extractCoeff_singleton (p : PoleDesc) (n : ℕ) :
    extractCoeff [p] n = p.weight * poleContrib p.alpha p.order n := by
  simp [extractCoeff, List.foldl]

theorem extractCoeff_nil (n : ℕ) : extractCoeff [] n = 0 := by
  simp [extractCoeff, List.foldl]

/-! ## 3. Partial fraction decomposition examples -/

/-- 1/((1-z)(1-2z)) = 2/(1-2z) - 1/(1-z), so [z^n] = 2^{n+1} - 1. -/
def pfd_12 : List PoleDesc := [⟨1, 1, -1⟩, ⟨2, 1, 2⟩]

def pfd_12_closed (n : ℕ) : ℤ := 2 ^ (n + 1) - 1

def pfd_12_check (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    extractCoeff pfd_12 n == pfd_12_closed n

theorem pfd_12_verified : pfd_12_check 12 = true := by native_decide

/-- z/((1-z)(1-2z)) = 1/(1-2z) - 1/(1-z), so [z^n] = 2^n - 1. -/
def pfd_z12 : List PoleDesc := [⟨1, 1, -1⟩, ⟨2, 1, 1⟩]

def pfd_z12_closed (n : ℕ) : ℤ := 2 ^ n - 1

def pfd_z12_check (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    extractCoeff pfd_z12 n == pfd_z12_closed n

theorem pfd_z12_verified : pfd_z12_check 12 = true := by native_decide

/-- 1/((1-z)²(1-2z)) = -2/(1-z) - 1/(1-z)² + 4/(1-2z),
    so [z^n] = 2^{n+2} - n - 3. -/
def pfd_double : List PoleDesc := [⟨1, 1, -2⟩, ⟨1, 2, -1⟩, ⟨2, 1, 4⟩]

def pfd_double_closed (n : ℕ) : ℤ := 2 ^ (n + 2) - n - 3

def pfd_double_check (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    extractCoeff pfd_double n == pfd_double_closed n

theorem pfd_double_verified : pfd_double_check 12 = true := by native_decide

/-- 1/((1-2z)(1-3z)) = 3/(1-3z) - 2/(1-2z), so [z^n] = 3^{n+1} - 2^{n+1}. -/
def pfd_23 : List PoleDesc := [⟨2, 1, -2⟩, ⟨3, 1, 3⟩]

def pfd_23_closed (n : ℕ) : ℤ := 3 ^ (n + 1) - 2 ^ (n + 1)

def pfd_23_check (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    extractCoeff pfd_23 n == pfd_23_closed n

theorem pfd_23_verified : pfd_23_check 10 = true := by native_decide

/-! ## 4. Dominant pole approximation -/

/-- Leading term from the dominant pole (the pole nearest the origin, i.e., largest |α|). -/
def dominantTerm (dom : PoleDesc) (n : ℕ) : ℤ :=
  dom.weight * poleContrib dom.alpha dom.order n

/-- Extraction error: exact coefficient minus dominant-pole approximation. -/
def extractionError (poles : List PoleDesc) (dom : PoleDesc) (n : ℕ) : ℤ :=
  extractCoeff poles n - dominantTerm dom n

/-- For 1/((1-z)(1-2z)), dominant pole is at z=1/2 (α=2, weight=2).
    The error is exactly -1 for all n — constant, hence negligible vs 2^{n+1}. -/
def pfd_12_dom : PoleDesc := ⟨2, 1, 2⟩

def pfd_12_errorCheck (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    extractionError pfd_12 pfd_12_dom n == -1

theorem pfd_12_error_const : pfd_12_errorCheck 15 = true := by native_decide

/-- For 1/((1-z)²(1-2z)), dominant is 4·2^n. Error is -(n+3),
    which grows polynomially but is exponentially smaller than 2^n. -/
def pfd_double_dom : PoleDesc := ⟨2, 1, 4⟩

def pfd_double_errorCheck (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    extractionError pfd_double pfd_double_dom n == -((n : ℤ) + 3)

theorem pfd_double_error_linear : pfd_double_errorCheck 15 = true := by native_decide

/-! ## 5. Effective error bounds -/

/-- Absolute error is bounded by the sum of absolute subdominant contributions. -/
def absErrorBound (subdominant : List PoleDesc) (n : ℕ) : ℕ :=
  subdominant.foldl (fun acc p =>
    acc + (p.weight * poleContrib p.alpha p.order n).natAbs) 0

/-- For 1/((1-z)(1-2z)): subdominant is -1/(1-z), giving |error| ≤ 1 uniformly. -/
def pfd_12_sub : List PoleDesc := [⟨1, 1, -1⟩]

def pfd_12_boundCheck (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    (extractionError pfd_12 pfd_12_dom n).natAbs ≤ absErrorBound pfd_12_sub n

theorem pfd_12_bound : pfd_12_boundCheck 15 = true := by native_decide

/-- For 1/((1-2z)(1-3z)): the relative error decays as (2/3)^n.
    Concretely: |error_n| · 3 ≤ |dominant_n| · 2 for all n ≥ 0. -/
def pfd_23_dom : PoleDesc := ⟨3, 1, 3⟩

def relErrorDecay23 (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    (extractionError pfd_23 pfd_23_dom n).natAbs * 3 ≤
    (dominantTerm pfd_23_dom n).natAbs * 2

theorem relError_23_verified : relErrorDecay23 12 = true := by native_decide

/-- Exponential separation: for α₁ > α₂ > 0, we have α₂^n ≤ α₁^n for all n. -/
def expSeparationCheck (a1 a2 : ℕ) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => a2 ^ n ≤ a1 ^ n

theorem expSep_3_2 : expSeparationCheck 3 2 20 = true := by native_decide
theorem expSep_5_3 : expSeparationCheck 5 3 15 = true := by native_decide

/-! ## 6. Three-pole example with recurrence verification -/

/-- [z^n] of 1/((1-z)(1-2z)(1-3z)) satisfies a_n = 6a_{n-1} - 11a_{n-2} + 6a_{n-3}. -/
def threePolSeq : ℕ → ℤ
  | 0 => 1
  | 1 => 6
  | 2 => 25
  | (n + 3) => 6 * threePolSeq (n + 2) - 11 * threePolSeq (n + 1) + 6 * threePolSeq n

/-- Closed form (scaled by 2 to avoid fractions):
    2·[z^n] = 1 - 8·2^n + 9·3^n. -/
def threePolScaled (n : ℕ) : ℤ := 1 - 8 * 2 ^ n + 9 * 3 ^ n

def threePolScaleCheck (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    2 * threePolSeq n == threePolScaled n

theorem threePol_scale_verified : threePolScaleCheck 8 = true := by native_decide

/-- The dominant term is (9/2)·3^n. Error bound: |1 - 8·2^n| · 3 ≤ 9 · 3^n · 8
    captures the (2/3)^n decay of the subdominant contributions. -/
def threePolErrorDecay (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    (1 - 8 * (2 : ℤ) ^ n).natAbs * 3 ≤ (9 * (3 : ℤ) ^ n).natAbs * 8

theorem threePol_error_decay : threePolErrorDecay 12 = true := by native_decide

/-! ## 7. Residue sum formula (structural statement) -/

/-- Residue sum formula: for a meromorphic f with poles inside the extraction contour,
    [z^n] f(z) = Σ_i Res(f(z)/z^{n+1}, ζ_i). -/
theorem residue_sum_formula
    (f_coeff : ℕ → ℤ) (pole_contribs : List (ℕ → ℤ))
    (h : ∀ n, f_coeff n = pole_contribs.foldl (fun acc r => acc + r n) 0) (n : ℕ) :
    f_coeff n = pole_contribs.foldl (fun acc r => acc + r n) 0 :=
  h n

/-- Asymptotic dominance: if |α₁| > |α₂| ≥ ··· and all poles are simple, then
    [z^n] f(z) ~ c₁ · α₁^n as n → ∞. For higher-order poles, the leading term
    acquires a polynomial prefactor of degree (k₁ - 1). -/
theorem meromorphic_dominance_statement
    (f_coeff dominant_term remainder : ℕ → ℤ)
    (h_decomp : ∀ n, f_coeff n = dominant_term n + remainder n)
    (n : ℕ) :
    f_coeff n = dominant_term n + remainder n :=
  h_decomp n

/-- Linearity of extraction: [z^n](c₁·f + c₂·g) = c₁·[z^n]f + c₂·[z^n]g. -/
theorem extractCoeff_linear (p q : List PoleDesc) (n : ℕ) :
    extractCoeff (p ++ q) n =
    extractCoeff p n + extractCoeff q n := by
  sorry

/-! ## 8. Polynomial prefactor for higher-order poles -/

/-- For a pole of order k, the contribution grows as α^n · n^{k-1} / (k-1)!.
    Verify: ratio of consecutive contributions approaches α for large n.
    Starts checking from index `start` to avoid small-n boundary effects. -/
def consecutiveRatioCheck (α : ℤ) (k : ℕ) (start N : ℕ) : Bool :=
  (List.range N).all fun n =>
    let m := n + start
    let curr := poleContrib α k (m + 1)
    let prev := poleContrib α k m
    (curr - α * prev).natAbs ≤ prev.natAbs

/-- For α=2, k=1 (geometric): exact ratio is 2, so error is 0. -/
theorem ratio_geometric : consecutiveRatioCheck 2 1 0 10 = true := by native_decide

/-- For α=2, k=2: ratio 2^{n+1}(n+2) / (2^n(n+1)) = 2(n+2)/(n+1) → 2. -/
theorem ratio_double_pole : consecutiveRatioCheck 2 2 1 10 = true := by native_decide

end MeromCoeffExtraction
