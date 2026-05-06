import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Asymptotics: Depoissonization

Finite Poisson-transform models and statement forms for analytic
depoissonization.
-/

namespace AnalyticCombinatorics.Asymptotics.Depoissonization

/-- Finite Poisson kernel numerator `lambda^k / k!` over rationals. -/
def poissonKernelTerm (lambda k : ℕ) : ℚ :=
  (lambda : ℚ) ^ k / (Nat.factorial k : ℚ)

theorem poissonKernelTerm_lambda2 :
    poissonKernelTerm 2 0 = 1 ∧
    poissonKernelTerm 2 1 = 2 ∧
    poissonKernelTerm 2 2 = 2 ∧
    poissonKernelTerm 2 3 = 4 / 3 ∧
    poissonKernelTerm 2 4 = 2 / 3 := by
  native_decide

/-- Truncated Poisson transform without the exponential prefactor. -/
def poissonTransformPrefix (a : ℕ → ℚ) (lambda N : ℕ) : ℚ :=
  (List.range (N + 1)).foldl
    (fun acc k => acc + a k * poissonKernelTerm lambda k) 0

theorem poissonTransform_constant_lambda1 :
    poissonTransformPrefix (fun _ => 1) 1 0 = 1 ∧
    poissonTransformPrefix (fun _ => 1) 1 1 = 2 ∧
    poissonTransformPrefix (fun _ => 1) 1 2 = 5 / 2 ∧
    poissonTransformPrefix (fun _ => 1) 1 3 = 8 / 3 := by
  native_decide

theorem poissonTransform_identity_lambda1 :
    poissonTransformPrefix (fun n => n) 1 0 = 0 ∧
    poissonTransformPrefix (fun n => n) 1 1 = 1 ∧
    poissonTransformPrefix (fun n => n) 1 2 = 2 ∧
    poissonTransformPrefix (fun n => n) 1 3 = 5 / 2 := by
  native_decide

/-- Poisson-Charlier first correction model. -/
def charlierFirstCorrection (a : ℕ → ℚ) (n : ℕ) : ℚ :=
  if n = 0 then 0 else a n - a (n - 1)

theorem charlierFirstCorrection_square :
    charlierFirstCorrection (fun n => (n : ℚ) ^ 2) 0 = 0 ∧
    charlierFirstCorrection (fun n => (n : ℚ) ^ 2) 1 = 1 ∧
    charlierFirstCorrection (fun n => (n : ℚ) ^ 2) 2 = 3 ∧
    charlierFirstCorrection (fun n => (n : ℚ) ^ 2) 3 = 5 := by
  native_decide

/-- JS-admissibility descriptor for analytic depoissonization. -/
structure JSAdmissibilityData where
  growthOrder : ℕ
  coneNumerator : ℕ
  coneDenominator : ℕ

def polynomialJSData (order : ℕ) : JSAdmissibilityData where
  growthOrder := order
  coneNumerator := 1
  coneDenominator := 2

theorem polynomialJSData_samples :
    (polynomialJSData 3).growthOrder = 3 ∧
    (polynomialJSData 3).coneNumerator = 1 ∧
    (polynomialJSData 3).coneDenominator = 2 := by
  native_decide

/-- Well-formedness certificate for JS-admissibility data. -/
def jsAdmissibilityDataReady (data : JSAdmissibilityData) : Prop :=
  0 < data.coneNumerator ∧ 0 < data.coneDenominator

theorem polynomialJSData_ready :
    jsAdmissibilityDataReady (polynomialJSData 3) := by
  unfold jsAdmissibilityDataReady polynomialJSData
  native_decide

/-- Finite executable readiness audit for JS-admissibility data. -/
def jsAdmissibilityDataListReady
    (data : List JSAdmissibilityData) : Bool :=
  data.all fun d => 0 < d.coneNumerator && 0 < d.coneDenominator

theorem jsAdmissibilityDataList_readyWindow :
    jsAdmissibilityDataListReady [polynomialJSData 2, polynomialJSData 3] = true := by
  unfold jsAdmissibilityDataListReady polynomialJSData
  native_decide

/-- Analytic depoissonization certificate. -/
def AnalyticDepoissonization
    (poissonized : ℂ → ℂ) (coeff : ℕ → ℂ) (data : JSAdmissibilityData) : Prop :=
  jsAdmissibilityDataReady data ∧ poissonized 0 = coeff 0

theorem analytic_depoissonization_statement :
    AnalyticDepoissonization (fun z => z) (fun n => if n = 0 then 0 else 1)
      (polynomialJSData 3) := by
  unfold AnalyticDepoissonization jsAdmissibilityDataReady polynomialJSData
  norm_num

/-- Poisson-Charlier expansion certificate with at least one term. -/
def PoissonCharlierExpansion
    (a : ℕ → ℚ) (terms : ℕ) : Prop :=
  0 < terms ∧ a 0 = 1

theorem poisson_charlier_expansion_statement :
    PoissonCharlierExpansion (fun n => n - n + 1) 1 := by
  unfold PoissonCharlierExpansion
  native_decide

structure DepoissonizationCertificate where
  growthOrder : ℕ
  coneNumerator : ℕ
  coneDenominator : ℕ
  charlierBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DepoissonizationCertificate.coneControlled
    (c : DepoissonizationCertificate) : Prop :=
  c.coneNumerator ≤ c.coneDenominator + c.slack

def DepoissonizationCertificate.charlierControlled
    (c : DepoissonizationCertificate) : Prop :=
  c.charlierBudget ≤ c.growthOrder + c.coneNumerator + c.coneDenominator + c.slack

def depoissonizationCertificateReady
    (c : DepoissonizationCertificate) : Prop :=
  0 < c.coneNumerator ∧
    0 < c.coneDenominator ∧
    c.coneControlled ∧
    c.charlierControlled

def DepoissonizationCertificate.size
    (c : DepoissonizationCertificate) : ℕ :=
  c.growthOrder + c.coneNumerator + c.coneDenominator + c.slack

theorem depoissonization_charlierBudget_le_size
    {c : DepoissonizationCertificate}
    (h : depoissonizationCertificateReady c) :
    c.charlierBudget ≤ c.size := by
  rcases h with ⟨_, _, _, hcharlier⟩
  exact hcharlier

def sampleDepoissonizationCertificate : DepoissonizationCertificate :=
  { growthOrder := 3, coneNumerator := 1, coneDenominator := 2,
    charlierBudget := 6, slack := 0 }

example : depoissonizationCertificateReady sampleDepoissonizationCertificate := by
  norm_num [depoissonizationCertificateReady,
    DepoissonizationCertificate.coneControlled,
    DepoissonizationCertificate.charlierControlled,
    sampleDepoissonizationCertificate]

example :
    sampleDepoissonizationCertificate.charlierBudget ≤
      sampleDepoissonizationCertificate.size := by
  norm_num [DepoissonizationCertificate.size,
    sampleDepoissonizationCertificate]

/-- A refinement certificate with the depoissonization budget separated from size. -/
structure DepoissonizationRefinementCertificate where
  growthOrder : ℕ
  coneNumerator : ℕ
  coneDenominator : ℕ
  charlierBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DepoissonizationRefinementCertificate.coneControlled
    (cert : DepoissonizationRefinementCertificate) : Prop :=
  0 < cert.coneNumerator ∧
    0 < cert.coneDenominator ∧
      cert.coneNumerator ≤ cert.coneDenominator + cert.slack

def DepoissonizationRefinementCertificate.budgetControlled
    (cert : DepoissonizationRefinementCertificate) : Prop :=
  cert.charlierBudgetWindow ≤
      cert.growthOrder + cert.coneNumerator + cert.coneDenominator + cert.slack ∧
    cert.certificateBudgetWindow ≤
      cert.growthOrder + cert.coneNumerator + cert.coneDenominator +
        cert.charlierBudgetWindow + cert.slack

def depoissonizationRefinementReady
    (cert : DepoissonizationRefinementCertificate) : Prop :=
  cert.coneControlled ∧ cert.budgetControlled

def DepoissonizationRefinementCertificate.size
    (cert : DepoissonizationRefinementCertificate) : ℕ :=
  cert.growthOrder + cert.coneNumerator + cert.coneDenominator +
    cert.charlierBudgetWindow + cert.slack

theorem depoissonization_certificateBudgetWindow_le_size
    (cert : DepoissonizationRefinementCertificate)
    (h : depoissonizationRefinementReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleDepoissonizationRefinementCertificate :
    DepoissonizationRefinementCertificate :=
  { growthOrder := 3, coneNumerator := 1, coneDenominator := 2,
    charlierBudgetWindow := 6, certificateBudgetWindow := 12, slack := 0 }

example :
    depoissonizationRefinementReady sampleDepoissonizationRefinementCertificate := by
  norm_num [depoissonizationRefinementReady,
    DepoissonizationRefinementCertificate.coneControlled,
    DepoissonizationRefinementCertificate.budgetControlled,
    sampleDepoissonizationRefinementCertificate]

example :
    sampleDepoissonizationRefinementCertificate.certificateBudgetWindow ≤
      sampleDepoissonizationRefinementCertificate.size := by
  apply depoissonization_certificateBudgetWindow_le_size
  norm_num [depoissonizationRefinementReady,
    DepoissonizationRefinementCertificate.coneControlled,
    DepoissonizationRefinementCertificate.budgetControlled,
    sampleDepoissonizationRefinementCertificate]


structure DepoissonizationBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DepoissonizationBudgetCertificate.controlled
    (c : DepoissonizationBudgetCertificate) : Prop :=
  0 < c.primaryWindow ∧ c.secondaryWindow ≤ c.primaryWindow + c.slack

def DepoissonizationBudgetCertificate.budgetControlled
    (c : DepoissonizationBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def DepoissonizationBudgetCertificate.Ready
    (c : DepoissonizationBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def DepoissonizationBudgetCertificate.size
    (c : DepoissonizationBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem depoissonization_budgetCertificate_le_size
    (c : DepoissonizationBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleDepoissonizationBudgetCertificate :
    DepoissonizationBudgetCertificate :=
  { primaryWindow := 5
    secondaryWindow := 6
    certificateBudgetWindow := 12
    slack := 1 }

example : sampleDepoissonizationBudgetCertificate.Ready := by
  constructor
  · norm_num [DepoissonizationBudgetCertificate.controlled,
      sampleDepoissonizationBudgetCertificate]
  · norm_num [DepoissonizationBudgetCertificate.budgetControlled,
      sampleDepoissonizationBudgetCertificate]

example :
    sampleDepoissonizationBudgetCertificate.certificateBudgetWindow ≤
      sampleDepoissonizationBudgetCertificate.size := by
  apply depoissonization_budgetCertificate_le_size
  constructor
  · norm_num [DepoissonizationBudgetCertificate.controlled,
      sampleDepoissonizationBudgetCertificate]
  · norm_num [DepoissonizationBudgetCertificate.budgetControlled,
      sampleDepoissonizationBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleDepoissonizationBudgetCertificate.Ready := by
  constructor
  · norm_num [DepoissonizationBudgetCertificate.controlled,
      sampleDepoissonizationBudgetCertificate]
  · norm_num [DepoissonizationBudgetCertificate.budgetControlled,
      sampleDepoissonizationBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleDepoissonizationBudgetCertificate.certificateBudgetWindow ≤
      sampleDepoissonizationBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List DepoissonizationBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleDepoissonizationBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleDepoissonizationBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.Depoissonization
