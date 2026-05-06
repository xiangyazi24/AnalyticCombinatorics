import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Bivariate generating functions.

Finite coefficient-window bookkeeping for size and parameter variables.
-/

namespace AnalyticCombinatorics.PartA.Ch3.BivariateGeneratingFunctions

/-- Bivariate coefficient table for a product of two geometric series. -/
def bivariateCoeff (xBase yBase i j : ℕ) : ℕ :=
  xBase ^ i * yBase ^ j

/-- Row sum over the parameter variable. -/
def parameterRowSum (a : ℕ → ℕ → ℕ) (i J : ℕ) : ℕ :=
  (List.range (J + 1)).foldl (fun total j => total + a i j) 0

/-- Finite envelope for bivariate coefficient tables. -/
def bivariateEnvelopeCheck
    (a : ℕ → ℕ → ℕ) (xBase yBase N : ℕ) : Bool :=
  (List.range (N + 1)).all fun i =>
    (List.range (N + 1)).all fun j =>
      a i j ≤ xBase ^ i * yBase ^ j

theorem bivariateCoeff_envelope :
    bivariateEnvelopeCheck (bivariateCoeff 2 3) 2 3 8 = true := by
  unfold bivariateEnvelopeCheck bivariateCoeff
  native_decide

theorem parameterRowSum_sample :
    parameterRowSum (bivariateCoeff 2 3) 2 2 = 52 := by
  unfold parameterRowSum bivariateCoeff
  native_decide

/-- Diagonal coefficient of a bivariate generating function. -/
def diagonalCoeff (a : ℕ → ℕ → ℕ) (n : ℕ) : ℕ :=
  a n n

theorem bivariateCoeff_diagonalRatioWindow :
    (List.range 8).all
      (fun n =>
        diagonalCoeff (bivariateCoeff 2 3) (n + 1) =
          6 * diagonalCoeff (bivariateCoeff 2 3) n) = true := by
  unfold diagonalCoeff bivariateCoeff
  native_decide

structure BivariateGFWindow where
  sizeDepth : ℕ
  parameterDepth : ℕ
  coefficientWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def bivariateGFReady (w : BivariateGFWindow) : Prop :=
  0 < w.sizeDepth ∧
    w.parameterDepth ≤ w.sizeDepth + w.coefficientWindow + w.slack

def bivariateGFBudget (w : BivariateGFWindow) : ℕ :=
  w.sizeDepth + w.parameterDepth + w.coefficientWindow + w.slack

theorem parameterDepth_le_budget (w : BivariateGFWindow) :
    w.parameterDepth ≤ bivariateGFBudget w := by
  unfold bivariateGFBudget
  omega

def sampleBivariateGFWindow : BivariateGFWindow :=
  { sizeDepth := 6, parameterDepth := 7, coefficientWindow := 4, slack := 1 }

example : bivariateGFReady sampleBivariateGFWindow := by
  norm_num [bivariateGFReady, sampleBivariateGFWindow]

structure BivariateGeneratingFunctionsBudgetCertificate where
  sizeWindow : ℕ
  parameterWindow : ℕ
  coefficientWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BivariateGeneratingFunctionsBudgetCertificate.controlled
    (c : BivariateGeneratingFunctionsBudgetCertificate) : Prop :=
  0 < c.sizeWindow ∧
    c.parameterWindow ≤ c.sizeWindow + c.coefficientWindow + c.slack

def BivariateGeneratingFunctionsBudgetCertificate.budgetControlled
    (c : BivariateGeneratingFunctionsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.sizeWindow + c.parameterWindow + c.coefficientWindow + c.slack

def BivariateGeneratingFunctionsBudgetCertificate.Ready
    (c : BivariateGeneratingFunctionsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BivariateGeneratingFunctionsBudgetCertificate.size
    (c : BivariateGeneratingFunctionsBudgetCertificate) : ℕ :=
  c.sizeWindow + c.parameterWindow + c.coefficientWindow + c.slack

theorem bivariateGeneratingFunctions_budgetCertificate_le_size
    (c : BivariateGeneratingFunctionsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleBivariateGeneratingFunctionsBudgetCertificate :
    BivariateGeneratingFunctionsBudgetCertificate :=
  { sizeWindow := 6
    parameterWindow := 7
    coefficientWindow := 4
    certificateBudgetWindow := 18
    slack := 1 }

example : sampleBivariateGeneratingFunctionsBudgetCertificate.Ready := by
  constructor
  · norm_num [BivariateGeneratingFunctionsBudgetCertificate.controlled,
      sampleBivariateGeneratingFunctionsBudgetCertificate]
  · norm_num [BivariateGeneratingFunctionsBudgetCertificate.budgetControlled,
      sampleBivariateGeneratingFunctionsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleBivariateGeneratingFunctionsBudgetCertificate.Ready := by
  constructor
  · norm_num [BivariateGeneratingFunctionsBudgetCertificate.controlled,
      sampleBivariateGeneratingFunctionsBudgetCertificate]
  · norm_num [BivariateGeneratingFunctionsBudgetCertificate.budgetControlled,
      sampleBivariateGeneratingFunctionsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleBivariateGeneratingFunctionsBudgetCertificate.certificateBudgetWindow ≤
      sampleBivariateGeneratingFunctionsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List BivariateGeneratingFunctionsBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleBivariateGeneratingFunctionsBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleBivariateGeneratingFunctionsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch3.BivariateGeneratingFunctions
