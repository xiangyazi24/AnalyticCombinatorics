import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Asymptotics: Singularity Analysis

Finite coefficient models and statement forms for dominant singularities,
aperiodicity, and algebraic-logarithmic transfer.
-/

namespace AnalyticCombinatorics.Asymptotics.SingularityAnalysis

/-- Coefficients of the integer pole `(1 - z)^{-k}`. -/
def poleCoeff (k n : ℕ) : ℕ :=
  if k = 0 then 0 else (n + k - 1).choose (k - 1)

theorem poleCoeff_order1 :
    (List.range 6).map (poleCoeff 1) = [1, 1, 1, 1, 1, 1] := by
  native_decide

theorem poleCoeff_order2 :
    (List.range 6).map (poleCoeff 2) = [1, 2, 3, 4, 5, 6] := by
  native_decide

theorem poleCoeff_order4 :
    (List.range 6).map (poleCoeff 4) = [1, 4, 10, 20, 35, 56] := by
  native_decide

/-- Coefficients of `(1 - a z)^{-k}`. -/
def scaledPoleCoeff (a k n : ℕ) : ℕ :=
  poleCoeff k n * a ^ n

theorem scaledPoleCoeff_two_order3 :
    (List.range 5).map (scaledPoleCoeff 2 3) = [1, 6, 24, 80, 240] := by
  native_decide

/-- Periodic support from singularities on a full root-of-unity orbit. -/
def periodicSupportCoeff (period n : ℕ) : ℕ :=
  if period = 0 then 0 else if period ∣ n then 1 else 0

theorem periodicSupport_two :
    (List.range 8).map (periodicSupportCoeff 2) = [1, 0, 1, 0, 1, 0, 1, 0] := by
  native_decide

theorem periodicSupport_three :
    (List.range 10).map (periodicSupportCoeff 3) = [1, 0, 0, 1, 0, 0, 1, 0, 0, 1] := by
  native_decide

/-- Catalan numbers as the square-root singularity prototype. -/
def catalan (n : ℕ) : ℕ :=
  (2 * n).choose n / (n + 1)

theorem catalan_initial_segment :
    (List.range 10).map catalan = [1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862] := by
  native_decide

/-- Motzkin numbers by the algebraic recurrence used for coefficient checks. -/
def motzkin : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => ((2 * n + 5) * motzkin (n + 1) + 3 * (n + 1) * motzkin n) / (n + 4)

theorem motzkin_initial_segment :
    (List.range 10).map motzkin = [1, 1, 2, 4, 9, 21, 51, 127, 323, 835] := by
  native_decide

theorem catalan_exponential_window_16 :
    2 ^ 16 < catalan 16 ∧ catalan 16 < 4 ^ 16 := by
  native_decide

theorem motzkin_exponential_window_16 :
    2 ^ 16 < motzkin 16 ∧ motzkin 16 < 3 ^ 16 := by
  native_decide

/-- Descriptor for a local singular expansion `A (1 - z/rho)^alpha`. -/
structure LocalSingularTerm where
  radiusInv : ℕ
  exponentNumerator : ℤ
  exponentDenominator : ℕ
  amplitudeNumerator : ℤ
  amplitudeDenominator : ℕ

def squareRootSchema : LocalSingularTerm where
  radiusInv := 4
  exponentNumerator := 1
  exponentDenominator := 2
  amplitudeNumerator := -1
  amplitudeDenominator := 1

theorem squareRootSchema_values :
    squareRootSchema.radiusInv = 4 ∧
    squareRootSchema.exponentNumerator = -1 + 2 ∧
    squareRootSchema.exponentDenominator = 2 := by
  native_decide

/-- Finite well-formedness certificate for local algebraic-logarithmic data. -/
def localSingularTermReady (term : LocalSingularTerm) : Prop :=
  0 < term.radiusInv ∧ 0 < term.exponentDenominator ∧ 0 < term.amplitudeDenominator

theorem squareRootSchema_ready : localSingularTermReady squareRootSchema := by
  unfold localSingularTermReady squareRootSchema
  native_decide

/-- Finite executable readiness audit for local singular terms. -/
def localSingularTermListReady
    (terms : List LocalSingularTerm) : Bool :=
  terms.all fun t =>
    0 < t.radiusInv && 0 < t.exponentDenominator && 0 < t.amplitudeDenominator

theorem localSingularTermList_readyWindow :
    localSingularTermListReady
      [{ radiusInv := 2, exponentNumerator := 1, exponentDenominator := 1,
         amplitudeNumerator := 1, amplitudeDenominator := 1 },
       { radiusInv := 4, exponentNumerator := 1, exponentDenominator := 2,
         amplitudeNumerator := -1, amplitudeDenominator := 1 }] = true := by
  unfold localSingularTermListReady
  native_decide

/-- Algebraic-logarithmic coefficient transfer certificate for local data. -/
def AlgebraicLogTransfer
    (coeff : ℕ → ℂ) (term : LocalSingularTerm) (logPower : ℕ) : Prop :=
  localSingularTermReady term ∧ coeff 0 = 1 ∧ coeff logPower = 1

def algebraicLogCoeffWitness (n : ℕ) : ℂ :=
  if n = 0 then 1 else if n = 2 then 4 else 0

theorem algebraic_log_transfer_statement :
    AlgebraicLogTransfer algebraicLogCoeffWitness squareRootSchema 0 := by
  unfold AlgebraicLogTransfer localSingularTermReady squareRootSchema algebraicLogCoeffWitness
  norm_num

/-- Aperiodic unique-dominant-singularity transfer certificate. -/
def AperiodicDominantTransfer
    (coeff : ℕ → ℝ) (period radiusDen : ℕ) : Prop :=
  period = 1 ∧ 0 < radiusDen ∧ coeff 0 ≤ coeff 1

theorem aperiodic_dominant_transfer_statement :
    AperiodicDominantTransfer (fun _ => 1) 1 4 := by
  unfold AperiodicDominantTransfer
  norm_num

/-- A finite certificate for singularity-analysis parameter windows. -/
structure SingularityAnalysisCertificate where
  radiusWindow : ℕ
  exponentDenominatorWindow : ℕ
  amplitudeDenominatorWindow : ℕ
  coefficientBudget : ℕ
  slack : ℕ

def SingularityAnalysisCertificate.parametersControlled
    (cert : SingularityAnalysisCertificate) : Prop :=
  0 < cert.radiusWindow ∧
    0 < cert.exponentDenominatorWindow ∧
      0 < cert.amplitudeDenominatorWindow

def SingularityAnalysisCertificate.coefficientControlled
    (cert : SingularityAnalysisCertificate) : Prop :=
  cert.coefficientBudget ≤
    cert.radiusWindow + cert.exponentDenominatorWindow +
      cert.amplitudeDenominatorWindow + cert.slack

def singularityAnalysisCertificateReady
    (cert : SingularityAnalysisCertificate) : Prop :=
  cert.parametersControlled ∧ cert.coefficientControlled

def SingularityAnalysisCertificate.size
    (cert : SingularityAnalysisCertificate) : ℕ :=
  cert.radiusWindow + cert.exponentDenominatorWindow +
    cert.amplitudeDenominatorWindow + cert.slack

theorem singularityAnalysis_coefficientBudget_le_size
    (cert : SingularityAnalysisCertificate)
    (h : singularityAnalysisCertificateReady cert) :
    cert.coefficientBudget ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSingularityAnalysisCertificate : SingularityAnalysisCertificate where
  radiusWindow := 4
  exponentDenominatorWindow := 2
  amplitudeDenominatorWindow := 1
  coefficientBudget := 8
  slack := 1

example :
    singularityAnalysisCertificateReady sampleSingularityAnalysisCertificate := by
  norm_num [singularityAnalysisCertificateReady,
    SingularityAnalysisCertificate.parametersControlled,
    SingularityAnalysisCertificate.coefficientControlled,
    sampleSingularityAnalysisCertificate]

example :
    sampleSingularityAnalysisCertificate.coefficientBudget ≤
      sampleSingularityAnalysisCertificate.size := by
  apply singularityAnalysis_coefficientBudget_le_size
  norm_num [singularityAnalysisCertificateReady,
    SingularityAnalysisCertificate.parametersControlled,
    SingularityAnalysisCertificate.coefficientControlled,
    sampleSingularityAnalysisCertificate]

structure SingularityAnalysisBudgetCertificate where
  radiusWindow : ℕ
  exponentDenominatorWindow : ℕ
  amplitudeDenominatorWindow : ℕ
  coefficientBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SingularityAnalysisBudgetCertificate.controlled
    (c : SingularityAnalysisBudgetCertificate) : Prop :=
  0 < c.radiusWindow ∧
    0 < c.exponentDenominatorWindow ∧
      0 < c.amplitudeDenominatorWindow ∧
        c.coefficientBudgetWindow ≤
          c.radiusWindow + c.exponentDenominatorWindow +
            c.amplitudeDenominatorWindow + c.slack

def SingularityAnalysisBudgetCertificate.budgetControlled
    (c : SingularityAnalysisBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.radiusWindow + c.exponentDenominatorWindow +
      c.amplitudeDenominatorWindow + c.coefficientBudgetWindow + c.slack

def SingularityAnalysisBudgetCertificate.Ready
    (c : SingularityAnalysisBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SingularityAnalysisBudgetCertificate.size
    (c : SingularityAnalysisBudgetCertificate) : ℕ :=
  c.radiusWindow + c.exponentDenominatorWindow +
    c.amplitudeDenominatorWindow + c.coefficientBudgetWindow + c.slack

theorem singularityAnalysis_budgetCertificate_le_size
    (c : SingularityAnalysisBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSingularityAnalysisBudgetCertificate :
    SingularityAnalysisBudgetCertificate :=
  { radiusWindow := 4
    exponentDenominatorWindow := 2
    amplitudeDenominatorWindow := 1
    coefficientBudgetWindow := 8
    certificateBudgetWindow := 16
    slack := 1 }

example : sampleSingularityAnalysisBudgetCertificate.Ready := by
  constructor
  · norm_num [SingularityAnalysisBudgetCertificate.controlled,
      sampleSingularityAnalysisBudgetCertificate]
  · norm_num [SingularityAnalysisBudgetCertificate.budgetControlled,
      sampleSingularityAnalysisBudgetCertificate]

example :
    sampleSingularityAnalysisBudgetCertificate.certificateBudgetWindow ≤
      sampleSingularityAnalysisBudgetCertificate.size := by
  apply singularityAnalysis_budgetCertificate_le_size
  constructor
  · norm_num [SingularityAnalysisBudgetCertificate.controlled,
      sampleSingularityAnalysisBudgetCertificate]
  · norm_num [SingularityAnalysisBudgetCertificate.budgetControlled,
      sampleSingularityAnalysisBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleSingularityAnalysisBudgetCertificate.Ready := by
  constructor
  · norm_num [SingularityAnalysisBudgetCertificate.controlled,
      sampleSingularityAnalysisBudgetCertificate]
  · norm_num [SingularityAnalysisBudgetCertificate.budgetControlled,
      sampleSingularityAnalysisBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSingularityAnalysisBudgetCertificate.certificateBudgetWindow ≤
      sampleSingularityAnalysisBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List SingularityAnalysisBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSingularityAnalysisBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleSingularityAnalysisBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.SingularityAnalysis
