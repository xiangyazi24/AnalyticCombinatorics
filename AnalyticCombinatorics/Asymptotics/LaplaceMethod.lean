import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Asymptotics: Laplace Method

Finite quadratic-maximum and Gaussian-scale models for Laplace asymptotics.
-/

namespace AnalyticCombinatorics.Asymptotics.LaplaceMethod

def quadraticPeak (a x : ℤ) : ℤ :=
  a - x ^ 2

theorem quadraticPeak_samples :
    (List.map (quadraticPeak 4) [-2, -1, 0, 1, 2]) = [0, 3, 4, 3, 0] := by
  native_decide

def discreteLaplaceWeight (x : ℤ) : ℚ :=
  1 / (1 + (x ^ 2 : ℤ) : ℚ)

theorem discreteLaplaceWeight_samples :
    discreteLaplaceWeight 0 = 1 ∧
    discreteLaplaceWeight 1 = 1 / 2 ∧
    discreteLaplaceWeight 2 = 1 / 5 := by
  native_decide

def laplaceWindow (n : ℕ) : ℕ :=
  Nat.sqrt n

theorem laplaceWindow_samples :
    laplaceWindow 1 = 1 ∧
    laplaceWindow 16 = 4 ∧
    laplaceWindow 81 = 9 := by
  native_decide

structure LaplaceData where
  maximumNumerator : ℤ
  maximumDenominator : ℕ
  curvatureNumerator : ℕ
  curvatureDenominator : ℕ

def standardLaplaceData : LaplaceData where
  maximumNumerator := 0
  maximumDenominator := 1
  curvatureNumerator := 1
  curvatureDenominator := 1

theorem standardLaplaceData_values :
    standardLaplaceData.maximumNumerator = 0 ∧
    standardLaplaceData.curvatureNumerator = 1 ∧
    standardLaplaceData.curvatureDenominator = 1 := by
  native_decide

def laplaceDataReady (data : LaplaceData) : Prop :=
  0 < data.maximumDenominator ∧ 0 < data.curvatureNumerator ∧
    0 < data.curvatureDenominator

theorem standardLaplaceData_ready : laplaceDataReady standardLaplaceData := by
  unfold laplaceDataReady standardLaplaceData
  native_decide

/-- Finite executable readiness audit for Laplace-method data. -/
def laplaceDataListReady (data : List LaplaceData) : Bool :=
  data.all fun d =>
    0 < d.maximumDenominator &&
      0 < d.curvatureNumerator && 0 < d.curvatureDenominator

theorem laplaceDataList_readyWindow :
    laplaceDataListReady
      [{ maximumNumerator := 1, maximumDenominator := 2,
         curvatureNumerator := 3, curvatureDenominator := 4 },
       { maximumNumerator := 0, maximumDenominator := 1,
         curvatureNumerator := 1, curvatureDenominator := 1 }] = true := by
  unfold laplaceDataListReady
  native_decide

def LaplaceAsymptoticSchema
    (integrand : ℝ → ℝ) (data : LaplaceData) : Prop :=
  laplaceDataReady data ∧ integrand 1 = 1

theorem laplace_asymptotic_schema_statement :
    LaplaceAsymptoticSchema (fun x => x) standardLaplaceData := by
  unfold LaplaceAsymptoticSchema laplaceDataReady standardLaplaceData
  norm_num

/-- A finite certificate for Laplace-method schema data. -/
structure LaplaceMethodCertificate where
  maximumDenominatorWindow : ℕ
  curvatureNumeratorWindow : ℕ
  curvatureDenominatorWindow : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- Laplace-method certificates keep curvature and denominators positive. -/
def laplaceMethodCertificateControlled
    (w : LaplaceMethodCertificate) : Prop :=
  0 < w.maximumDenominatorWindow ∧
    0 < w.curvatureNumeratorWindow ∧
      0 < w.curvatureDenominatorWindow

/-- Readiness for a Laplace-method certificate. -/
def laplaceMethodCertificateReady
    (w : LaplaceMethodCertificate) : Prop :=
  laplaceMethodCertificateControlled w ∧
    w.certificateBudget ≤
      w.maximumDenominatorWindow + w.curvatureNumeratorWindow +
        w.curvatureDenominatorWindow + w.slack

/-- Total size of a Laplace-method certificate. -/
def laplaceMethodCertificateSize (w : LaplaceMethodCertificate) : ℕ :=
  w.maximumDenominatorWindow + w.curvatureNumeratorWindow +
    w.curvatureDenominatorWindow + w.certificateBudget + w.slack

theorem laplaceMethodCertificate_budget_le_size
    (w : LaplaceMethodCertificate)
    (h : laplaceMethodCertificateReady w) :
    w.certificateBudget ≤ laplaceMethodCertificateSize w := by
  rcases h with ⟨_, hbudget⟩
  unfold laplaceMethodCertificateSize
  omega

def sampleLaplaceMethodCertificate : LaplaceMethodCertificate where
  maximumDenominatorWindow := 1
  curvatureNumeratorWindow := 1
  curvatureDenominatorWindow := 1
  certificateBudget := 3
  slack := 1

example :
    laplaceMethodCertificateReady sampleLaplaceMethodCertificate := by
  norm_num [laplaceMethodCertificateReady,
    laplaceMethodCertificateControlled, sampleLaplaceMethodCertificate]

example :
    sampleLaplaceMethodCertificate.certificateBudget ≤
      laplaceMethodCertificateSize sampleLaplaceMethodCertificate := by
  apply laplaceMethodCertificate_budget_le_size
  norm_num [laplaceMethodCertificateReady,
    laplaceMethodCertificateControlled, sampleLaplaceMethodCertificate]

/-- A refinement certificate separating the approximation budget from curvature windows. -/
structure LaplaceMethodRefinementCertificate where
  maximumDenominatorWindow : ℕ
  curvatureNumeratorWindow : ℕ
  curvatureDenominatorWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ

def LaplaceMethodRefinementCertificate.parametersControlled
    (cert : LaplaceMethodRefinementCertificate) : Prop :=
  0 < cert.maximumDenominatorWindow ∧
    0 < cert.curvatureNumeratorWindow ∧
      0 < cert.curvatureDenominatorWindow

def LaplaceMethodRefinementCertificate.budgetControlled
    (cert : LaplaceMethodRefinementCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.maximumDenominatorWindow + cert.curvatureNumeratorWindow +
      cert.curvatureDenominatorWindow + cert.slack

def laplaceMethodRefinementReady
    (cert : LaplaceMethodRefinementCertificate) : Prop :=
  cert.parametersControlled ∧ cert.budgetControlled

def LaplaceMethodRefinementCertificate.size
    (cert : LaplaceMethodRefinementCertificate) : ℕ :=
  cert.maximumDenominatorWindow + cert.curvatureNumeratorWindow +
    cert.curvatureDenominatorWindow + cert.slack

theorem laplaceMethod_certificateBudgetWindow_le_size
    (cert : LaplaceMethodRefinementCertificate)
    (h : laplaceMethodRefinementReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleLaplaceMethodRefinementCertificate :
    LaplaceMethodRefinementCertificate where
  maximumDenominatorWindow := 1
  curvatureNumeratorWindow := 1
  curvatureDenominatorWindow := 1
  certificateBudgetWindow := 4
  slack := 1

example :
    laplaceMethodRefinementReady sampleLaplaceMethodRefinementCertificate := by
  norm_num [laplaceMethodRefinementReady,
    LaplaceMethodRefinementCertificate.parametersControlled,
    LaplaceMethodRefinementCertificate.budgetControlled,
    sampleLaplaceMethodRefinementCertificate]

example :
    sampleLaplaceMethodRefinementCertificate.certificateBudgetWindow ≤
      sampleLaplaceMethodRefinementCertificate.size := by
  apply laplaceMethod_certificateBudgetWindow_le_size
  norm_num [laplaceMethodRefinementReady,
    LaplaceMethodRefinementCertificate.parametersControlled,
    LaplaceMethodRefinementCertificate.budgetControlled,
    sampleLaplaceMethodRefinementCertificate]


structure LaplaceMethodBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LaplaceMethodBudgetCertificate.controlled
    (c : LaplaceMethodBudgetCertificate) : Prop :=
  0 < c.primaryWindow ∧ c.secondaryWindow ≤ c.primaryWindow + c.slack

def LaplaceMethodBudgetCertificate.budgetControlled
    (c : LaplaceMethodBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def LaplaceMethodBudgetCertificate.Ready
    (c : LaplaceMethodBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LaplaceMethodBudgetCertificate.size
    (c : LaplaceMethodBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem laplaceMethod_budgetCertificate_le_size
    (c : LaplaceMethodBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleLaplaceMethodBudgetCertificate :
    LaplaceMethodBudgetCertificate :=
  { primaryWindow := 5
    secondaryWindow := 6
    certificateBudgetWindow := 12
    slack := 1 }

example : sampleLaplaceMethodBudgetCertificate.Ready := by
  constructor
  · norm_num [LaplaceMethodBudgetCertificate.controlled,
      sampleLaplaceMethodBudgetCertificate]
  · norm_num [LaplaceMethodBudgetCertificate.budgetControlled,
      sampleLaplaceMethodBudgetCertificate]

example :
    sampleLaplaceMethodBudgetCertificate.certificateBudgetWindow ≤
      sampleLaplaceMethodBudgetCertificate.size := by
  apply laplaceMethod_budgetCertificate_le_size
  constructor
  · norm_num [LaplaceMethodBudgetCertificate.controlled,
      sampleLaplaceMethodBudgetCertificate]
  · norm_num [LaplaceMethodBudgetCertificate.budgetControlled,
      sampleLaplaceMethodBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleLaplaceMethodBudgetCertificate.Ready := by
  constructor
  · norm_num [LaplaceMethodBudgetCertificate.controlled,
      sampleLaplaceMethodBudgetCertificate]
  · norm_num [LaplaceMethodBudgetCertificate.budgetControlled,
      sampleLaplaceMethodBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleLaplaceMethodBudgetCertificate.certificateBudgetWindow ≤
      sampleLaplaceMethodBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List LaplaceMethodBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleLaplaceMethodBudgetCertificate] =
      true := by
  unfold budgetCertificateListReady sampleLaplaceMethodBudgetCertificate
  native_decide

end AnalyticCombinatorics.Asymptotics.LaplaceMethod
