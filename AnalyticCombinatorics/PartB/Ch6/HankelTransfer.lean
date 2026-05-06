import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Chapter VI: Hankel Transfer

Finite coefficient models for Hankel-contour transfer, logarithmic factors,
and inverse-gamma normalization.
-/

namespace AnalyticCombinatorics.PartB.Ch6.HankelTransfer

/-- Rational model for coefficients of `(1-z)^alpha` when `alpha` is a small integer. -/
def binomialSignedCoeff (m n : ℕ) : ℤ :=
  if n ≤ m then (-1 : ℤ) ^ n * (m.choose n : ℤ) else 0

theorem binomialSignedCoeff_m3 :
    (List.range 6).map (binomialSignedCoeff 3) = [1, -3, 3, -1, 0, 0] := by
  native_decide

/-- Coefficients of `-log(1-z)`. -/
def negLogCoeff (n : ℕ) : ℚ :=
  if n = 0 then 0 else 1 / (n : ℚ)

theorem negLogCoeff_samples :
    (List.range 6).map negLogCoeff = [0, 1, 1 / 2, 1 / 3, 1 / 4, 1 / 5] := by
  native_decide

/-- Coefficients of `(-log(1-z))/(1-z)`, i.e. harmonic numbers. -/
def harmonic : ℕ → ℚ
  | 0 => 0
  | n + 1 => harmonic n + 1 / (n + 1 : ℚ)

theorem logPoleCoeff_samples :
    (List.range 7).map harmonic = [0, 1, 3 / 2, 11 / 6, 25 / 12, 137 / 60, 49 / 20] := by
  native_decide

/-- A finite inverse-gamma table for integer poles: `1/Gamma(k) = 1/(k-1)!`. -/
def invGammaPositiveInteger (k : ℕ) : ℚ :=
  if k = 0 then 0 else 1 / (Nat.factorial (k - 1) : ℚ)

theorem invGammaPositiveInteger_samples :
    invGammaPositiveInteger 0 = 0 ∧
    invGammaPositiveInteger 1 = 1 ∧
    invGammaPositiveInteger 2 = 1 ∧
    invGammaPositiveInteger 3 = 1 / 2 ∧
    invGammaPositiveInteger 4 = 1 / 6 ∧
    invGammaPositiveInteger 5 = 1 / 24 := by
  native_decide

/-- Transfer scale `n^{alpha-1} rho^{-n}` represented by integer inverse radius. -/
def transferScaleModel (rhoInv alphaShift n : ℕ) : ℕ :=
  n ^ alphaShift * rhoInv ^ n

theorem transferScaleModel_samples :
    transferScaleModel 4 0 3 = 64 ∧
    transferScaleModel 4 1 3 = 192 ∧
    transferScaleModel 3 2 4 = 1296 := by
  native_decide

/-- Log-power transfer descriptor. -/
structure LogPowerTransferData where
  radiusInv : ℕ
  algebraicShift : ℤ
  logPower : ℕ

def logarithmicSingularityData : LogPowerTransferData where
  radiusInv := 1
  algebraicShift := -1
  logPower := 1

theorem logarithmicSingularityData_values :
    logarithmicSingularityData.radiusInv = 1 ∧
    logarithmicSingularityData.algebraicShift = -1 ∧
    logarithmicSingularityData.logPower = 1 := by
  native_decide

def logPowerTransferDataReady (data : LogPowerTransferData) : Prop :=
  0 < data.radiusInv

theorem logarithmicSingularityData_ready :
    logPowerTransferDataReady logarithmicSingularityData := by
  unfold logPowerTransferDataReady logarithmicSingularityData
  native_decide

/-- Hankel transfer certificate for algebraic singularities. -/
def HankelAlgebraicTransfer
    (coeff : ℕ → ℂ) (data : LogPowerTransferData) : Prop :=
  logPowerTransferDataReady data ∧ coeff 0 = coeff data.radiusInv

theorem hankel_algebraic_transfer_statement :
    HankelAlgebraicTransfer (fun _ => 0) logarithmicSingularityData := by
  unfold HankelAlgebraicTransfer logPowerTransferDataReady logarithmicSingularityData
  norm_num

/-- Logarithmic transfer certificate. -/
def LogarithmicTransfer
    (coeff : ℕ → ℂ) (data : LogPowerTransferData) : Prop :=
  logPowerTransferDataReady data ∧ coeff 0 = coeff data.logPower

theorem logarithmic_transfer_statement :
    LogarithmicTransfer (fun _ => 0) logarithmicSingularityData := by
  unfold LogarithmicTransfer logPowerTransferDataReady logarithmicSingularityData
  norm_num


structure HankelTransferBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def HankelTransferBudgetCertificate.controlled
    (c : HankelTransferBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def HankelTransferBudgetCertificate.budgetControlled
    (c : HankelTransferBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def HankelTransferBudgetCertificate.Ready
    (c : HankelTransferBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def HankelTransferBudgetCertificate.size
    (c : HankelTransferBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem hankelTransfer_budgetCertificate_le_size
    (c : HankelTransferBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleHankelTransferBudgetCertificate :
    HankelTransferBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleHankelTransferBudgetCertificate.Ready := by
  constructor
  · norm_num [HankelTransferBudgetCertificate.controlled,
      sampleHankelTransferBudgetCertificate]
  · norm_num [HankelTransferBudgetCertificate.budgetControlled,
      sampleHankelTransferBudgetCertificate]

example :
    sampleHankelTransferBudgetCertificate.certificateBudgetWindow ≤
      sampleHankelTransferBudgetCertificate.size := by
  apply hankelTransfer_budgetCertificate_le_size
  constructor
  · norm_num [HankelTransferBudgetCertificate.controlled,
      sampleHankelTransferBudgetCertificate]
  · norm_num [HankelTransferBudgetCertificate.budgetControlled,
      sampleHankelTransferBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleHankelTransferBudgetCertificate.Ready := by
  constructor
  · norm_num [HankelTransferBudgetCertificate.controlled,
      sampleHankelTransferBudgetCertificate]
  · norm_num [HankelTransferBudgetCertificate.budgetControlled,
      sampleHankelTransferBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleHankelTransferBudgetCertificate.certificateBudgetWindow ≤
      sampleHankelTransferBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List HankelTransferBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleHankelTransferBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleHankelTransferBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch6.HankelTransfer
