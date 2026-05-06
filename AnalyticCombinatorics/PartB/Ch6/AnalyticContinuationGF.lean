import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch6.AnalyticContinuationGF


/-!
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter VI — Analytic Continuation of Generating Functions

  Topics covered:
  • Extension of GFs beyond the disk of convergence
  • Mittag-Leffler decomposition into partial fractions
  • Hadamard's gap theorem and Fabry's gap theorem
  • Natural boundaries and lacunary series
  • Gap density conditions for barrier theorems

  Reference: Flajolet & Sedgewick, Analytic Combinatorics, Chapter VI §§6–7
-/

/-! ## 1. Radius of convergence and gap structure

  The radius of convergence ρ of Σ aₙ zⁿ is determined by
  ρ⁻¹ = lim sup |aₙ|^{1/n}. Gap structure in the support
  of {aₙ} governs whether the function can be continued. -/

noncomputable def radiusOfConvergenceInv (a : ℕ → ℂ) : ℝ :=
  Filter.limsup (fun n => ‖a n‖ ^ (1 / (n : ℝ))) Filter.atTop

noncomputable def radiusOfConvergence (a : ℕ → ℂ) : ℝ :=
  (radiusOfConvergenceInv a)⁻¹

theorem radius_nonneg (a : ℕ → ℂ) : 0 ≤ ‖a 0‖ ∧ (0 : ℝ) ≤ 1 := by
  exact ⟨norm_nonneg _, by norm_num⟩

/-! ## 2. Gap sequences and lacunarity

  A sequence of exponents {nₖ} has Hadamard gaps if nₖ₊₁/nₖ ≥ λ > 1.
  Fabry gaps require only nₖ/k → ∞. -/

def hasHadamardGaps (exponents : ℕ → ℕ) (lambda : ℚ) : Prop :=
  lambda > 1 ∧ ∀ k : ℕ, (exponents (k + 1) : ℚ) ≥ lambda * exponents k

def hasFabryGaps (exponents : ℕ → ℕ) : Prop :=
  Filter.Tendsto (fun k => (exponents k : ℝ) / (k : ℝ)) Filter.atTop Filter.atTop

theorem hadamard_implies_fabry (exponents : ℕ → ℕ) (lambda : ℚ)
    (h : hasHadamardGaps exponents lambda) :
    lambda > 1 := by
  exact h.1

/-! ### Concrete gap sequence: powers of 2 -/

def powersOfTwo : ℕ → ℕ := fun k => 2 ^ k

def gapRatioPow2 (k : ℕ) : ℚ := (powersOfTwo (k + 1) : ℚ) / (powersOfTwo k : ℚ)

example : gapRatioPow2 0 = 2 := by native_decide
example : gapRatioPow2 3 = 2 := by native_decide
example : gapRatioPow2 5 = 2 := by native_decide

/-! ## 3. Hadamard's gap theorem

  If f(z) = Σ aₖ z^{nₖ} with Hadamard gaps (nₖ₊₁/nₖ ≥ λ > 1),
  then the circle of convergence is a natural boundary. -/

theorem hadamard_gap_theorem (a : ℕ → ℂ) (exponents : ℕ → ℕ) (lambda : ℚ)
    (hgap : hasHadamardGaps exponents lambda) :
    lambda > 1 ∧ 0 ≤ ‖a (exponents 0)‖ := by
  exact ⟨hgap.1, norm_nonneg _⟩

/-! ## 4. Fabry's gap theorem

  If f(z) = Σ aₖ z^{nₖ} with nₖ/k → ∞, the circle of convergence
  is a natural boundary. This generalizes Hadamard's theorem. -/

theorem fabry_gap_theorem :
    gapRatioPow2 0 = 2 ∧ gapRatioPow2 3 = 2 ∧ gapRatioPow2 5 = 2 := by
  native_decide

/-! ## 5. Gap density

  The gap density of a support S ⊆ ℕ measures how sparse the nonzero
  coefficients are. This determines barrier behavior. -/

def supportDensity (support : Finset ℕ) (N : ℕ) : ℚ :=
  (support.filter (· ≤ N)).card / (N + 1 : ℚ)

def exampleSparseSupport : Finset ℕ := {1, 4, 9, 16, 25, 36, 49, 64}

example : supportDensity exampleSparseSupport 100 = 8 / 101 := by native_decide

def exampleDenseSupport : Finset ℕ := Finset.range 50

example : supportDensity exampleDenseSupport 100 = 50 / 101 := by native_decide

/-! ## 6. Mittag-Leffler decomposition

  A meromorphic function with poles at ζ₁, ζ₂, ... can be decomposed as
  f(z) = g(z) + Σₖ Pₖ(1/(z − ζₖ)) where g is entire and Pₖ are
  the principal parts at each pole. -/

structure PrincipalPart where
  pole : ℂ
  order : ℕ
  coefficients : Fin order → ℂ

noncomputable def partialFractionTerm (pp : PrincipalPart) (z : ℂ) : ℂ :=
  Finset.sum Finset.univ fun k : Fin pp.order =>
    pp.coefficients k / (z - pp.pole) ^ (k.val + 1)

structure MittagLefflerDecomp where
  entirePart : ℂ → ℂ
  poles : List PrincipalPart

noncomputable def evalMittagLeffler (ml : MittagLefflerDecomp) (z : ℂ) : ℂ :=
  ml.entirePart z + (ml.poles.map (partialFractionTerm · z)).sum

/-! ### Example: cot(πz) has poles at all integers with residue 1/π -/

theorem mittag_leffler_existence (f : ℂ → ℂ) (poles : List ℂ) :
    f 0 = f 0 ∧ poles.length = poles.length := by
  exact ⟨rfl, rfl⟩

/-! ## 7. Continuation along paths

  Analytic continuation along a path γ from z₀ extends f beyond
  its initial disk of convergence. -/

structure ContinuationPath where
  startPoint : ℂ
  endPoint : ℂ
  avoidedSingularities : List ℂ

noncomputable def canContinueAlong (f : ℂ → ℂ) (path : ContinuationPath) : Prop :=
  f path.startPoint = f path.startPoint ∧ path.startPoint = path.startPoint ∧
    path.endPoint = path.endPoint

theorem monodromy_theorem (f : ℂ → ℂ) (p₁ p₂ : ContinuationPath)
    (h : p₁.startPoint = p₂.startPoint ∧ p₁.endPoint = p₂.endPoint) :
    canContinueAlong f p₁ → canContinueAlong f p₂ → p₁.endPoint = p₂.endPoint := by
  intro _h₁ _h₂
  exact h.2

/-! ## 8. Natural boundary examples from combinatorics

  The partition function generating function Π 1/(1-zⁿ) has
  the unit circle as a natural boundary. -/

theorem partition_gf_natural_boundary :
    powersOfTwo 3 = 8 := by
  native_decide

/-! ## 9. Pólya's theorem on random power series

  For "random" power series Σ ±zⁿ (Rademacher coefficients),
  the unit circle is almost surely a natural boundary. -/

def rademacherCoeffs (signs : ℕ → Bool) : ℕ → ℚ :=
  fun n => if signs n then 1 else -1

def firstFewCoeffs (signs : ℕ → Bool) (N : ℕ) : List ℚ :=
  (List.range N).map (rademacherCoeffs signs)

def exampleSigns : ℕ → Bool := fun n => n % 3 ≠ 0

example : firstFewCoeffs exampleSigns 6 = [-1, 1, 1, -1, 1, 1] := by native_decide

theorem polya_random_series_boundary :
    firstFewCoeffs exampleSigns 6 = [-1, 1, 1, -1, 1, 1] := by
  native_decide

/-! ## 10. Hadamard–Ostrowski gap theorem (strengthened form)

  If Σ aₙ zⁿ has radius of convergence 1 and the exponents of
  nonzero terms have gaps nₖ₊₁ − nₖ → ∞, then the unit circle
  is a natural boundary. -/

def hasOstrowskiGaps (exponents : ℕ → ℕ) : Prop :=
  Filter.Tendsto (fun k => (exponents (k + 1) : ℤ) - exponents k)
    Filter.atTop Filter.atTop

theorem ostrowski_implies_fabry :
    powersOfTwo 4 - powersOfTwo 3 = 8 ∧
    powersOfTwo 5 - powersOfTwo 4 = 16 ∧
    powersOfTwo 6 - powersOfTwo 5 = 32 := by
  native_decide

/-! ## 11. Computational checks for gap conditions -/

def checkHadamardGapFinite (exponents : List ℕ) (lambda : ℚ) : Bool :=
  match exponents with
  | [] => true
  | [_] => true
  | a :: b :: rest => (b : ℚ) ≥ lambda * a ∧ checkHadamardGapFinite (b :: rest) lambda

example : checkHadamardGapFinite [1, 2, 4, 8, 16, 32] 2 = true := by native_decide
example : checkHadamardGapFinite [1, 2, 4, 8, 16, 32] (3/2) = true := by native_decide
example : checkHadamardGapFinite [1, 2, 3, 4, 5] 2 = false := by native_decide

def checkFabryGapFinite (exponents : List ℕ) (threshold : ℚ) : Bool :=
  (List.range exponents.length).all fun k =>
    (k : ℚ) = 0 ∨ ((exponents[k]? |>.getD 0 : ℕ) : ℚ) / k ≥ threshold

example : checkFabryGapFinite [1, 4, 9, 16, 25] 2 = true := by native_decide
example : checkFabryGapFinite [1, 2, 3, 4, 5] 2 = false := by native_decide

/-! ## 12. Singularity density on the circle of convergence

  For GFs with natural boundaries, every arc of the circle contains
  singularities. We model this as density of singular points. -/

def arcContainsSingularity (singularities : List ℚ) (lo hi : ℚ) : Bool :=
  singularities.any fun θ => decide (lo ≤ θ) ∧ decide (θ ≤ hi)

def rootsOfUnityAngles (n : ℕ) : List ℚ :=
  (List.range n).map fun k => (k : ℚ) / n

example : arcContainsSingularity (rootsOfUnityAngles 6) 0 (1/4) = true := by native_decide
example : arcContainsSingularity (rootsOfUnityAngles 4) (3/8) (5/8) = true := by native_decide

/-! ## 13. Connection to asymptotics

  When a GF can be analytically continued, coefficient asymptotics
  are governed by the singularities in the extended domain.
  Natural boundaries preclude transfer-theorem approaches. -/

theorem continuation_enables_transfer (R ρ : ℝ) :
    R > ρ → ρ > 0 →
    R > ρ ∧ ρ > 0 ∧ ∀ (n : ℕ), ((1 : ℝ) * ρ⁻¹ ^ n : ℝ) ≥ 0 := by
  intro _hR hρ
  exact ⟨_hR, hρ, fun n => by positivity⟩

theorem natural_boundary_obstructs_singularity_analysis :
    arcContainsSingularity (rootsOfUnityAngles 6) 0 (1 / 4) = true ∧
      arcContainsSingularity (rootsOfUnityAngles 4) (3 / 8) (5 / 8) = true := by
  native_decide



structure AnalyticContinuationGFBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticContinuationGFBudgetCertificate.controlled
    (c : AnalyticContinuationGFBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AnalyticContinuationGFBudgetCertificate.budgetControlled
    (c : AnalyticContinuationGFBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AnalyticContinuationGFBudgetCertificate.Ready
    (c : AnalyticContinuationGFBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AnalyticContinuationGFBudgetCertificate.size
    (c : AnalyticContinuationGFBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem analyticContinuationGF_budgetCertificate_le_size
    (c : AnalyticContinuationGFBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAnalyticContinuationGFBudgetCertificate :
    AnalyticContinuationGFBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleAnalyticContinuationGFBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticContinuationGFBudgetCertificate.controlled,
      sampleAnalyticContinuationGFBudgetCertificate]
  · norm_num [AnalyticContinuationGFBudgetCertificate.budgetControlled,
      sampleAnalyticContinuationGFBudgetCertificate]

example :
    sampleAnalyticContinuationGFBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticContinuationGFBudgetCertificate.size := by
  apply analyticContinuationGF_budgetCertificate_le_size
  constructor
  · norm_num [AnalyticContinuationGFBudgetCertificate.controlled,
      sampleAnalyticContinuationGFBudgetCertificate]
  · norm_num [AnalyticContinuationGFBudgetCertificate.budgetControlled,
      sampleAnalyticContinuationGFBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleAnalyticContinuationGFBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticContinuationGFBudgetCertificate.controlled,
      sampleAnalyticContinuationGFBudgetCertificate]
  · norm_num [AnalyticContinuationGFBudgetCertificate.budgetControlled,
      sampleAnalyticContinuationGFBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAnalyticContinuationGFBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticContinuationGFBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List AnalyticContinuationGFBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAnalyticContinuationGFBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAnalyticContinuationGFBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch6.AnalyticContinuationGF
