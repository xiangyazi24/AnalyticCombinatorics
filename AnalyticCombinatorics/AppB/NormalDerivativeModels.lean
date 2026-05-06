import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Normal-derivative boundary bookkeeping.

The finite records are used for boundary maximum-principle arguments where
only derivative signs and boundary budgets are needed downstream.
-/

namespace AnalyticCombinatorics.AppB.NormalDerivativeModels

structure BoundaryDerivativeDatum where
  boundaryValue : ℕ
  normalDerivative : ℤ
  boundaryBudget : ℕ
deriving DecidableEq, Repr

def derivativePointsOutward (d : BoundaryDerivativeDatum) : Prop :=
  0 ≤ d.normalDerivative

def boundaryValueControlled (d : BoundaryDerivativeDatum) : Prop :=
  d.boundaryValue ≤ d.boundaryBudget

def boundaryDerivativeReady (d : BoundaryDerivativeDatum) : Prop :=
  derivativePointsOutward d ∧ boundaryValueControlled d

def boundarySlack (d : BoundaryDerivativeDatum) : ℕ :=
  d.boundaryBudget - d.boundaryValue

theorem boundaryDerivativeReady.controlled {d : BoundaryDerivativeDatum}
    (h : boundaryDerivativeReady d) :
    derivativePointsOutward d ∧ boundaryValueControlled d := by
  refine ⟨h.1, h.2⟩

theorem boundarySlack_add {d : BoundaryDerivativeDatum}
    (h : boundaryValueControlled d) :
    boundarySlack d + d.boundaryValue = d.boundaryBudget := by
  unfold boundarySlack boundaryValueControlled at *
  omega

def sampleBoundaryDerivative : BoundaryDerivativeDatum :=
  { boundaryValue := 4, normalDerivative := 2, boundaryBudget := 9 }

example : boundaryDerivativeReady sampleBoundaryDerivative := by
  norm_num
    [boundaryDerivativeReady, derivativePointsOutward, boundaryValueControlled,
      sampleBoundaryDerivative]

example : boundarySlack sampleBoundaryDerivative = 5 := by
  native_decide

structure NormalDerivativeWindow where
  boundaryWindow : ℕ
  derivativeWindow : ℕ
  signSlack : ℕ
  derivativeBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def NormalDerivativeWindow.derivativeControlled (w : NormalDerivativeWindow) : Prop :=
  w.derivativeWindow ≤ w.boundaryWindow + w.signSlack + w.slack

def normalDerivativeWindowReady (w : NormalDerivativeWindow) : Prop :=
  0 < w.boundaryWindow ∧ w.derivativeControlled ∧
    w.derivativeBudget ≤ w.boundaryWindow + w.derivativeWindow + w.slack

def NormalDerivativeWindow.certificate (w : NormalDerivativeWindow) : ℕ :=
  w.boundaryWindow + w.derivativeWindow + w.signSlack + w.derivativeBudget + w.slack

theorem normalDerivative_derivativeBudget_le_certificate (w : NormalDerivativeWindow) :
    w.derivativeBudget ≤ w.certificate := by
  unfold NormalDerivativeWindow.certificate
  omega

def sampleNormalDerivativeWindow : NormalDerivativeWindow :=
  { boundaryWindow := 5, derivativeWindow := 4, signSlack := 1,
    derivativeBudget := 10, slack := 1 }

example : normalDerivativeWindowReady sampleNormalDerivativeWindow := by
  norm_num [normalDerivativeWindowReady, NormalDerivativeWindow.derivativeControlled,
    sampleNormalDerivativeWindow]


structure NormalDerivativeModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def NormalDerivativeModelsBudgetCertificate.controlled
    (c : NormalDerivativeModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def NormalDerivativeModelsBudgetCertificate.budgetControlled
    (c : NormalDerivativeModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def NormalDerivativeModelsBudgetCertificate.Ready
    (c : NormalDerivativeModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def NormalDerivativeModelsBudgetCertificate.size
    (c : NormalDerivativeModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem normalDerivativeModels_budgetCertificate_le_size
    (c : NormalDerivativeModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleNormalDerivativeModelsBudgetCertificate :
    NormalDerivativeModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleNormalDerivativeModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [NormalDerivativeModelsBudgetCertificate.controlled,
      sampleNormalDerivativeModelsBudgetCertificate]
  · norm_num [NormalDerivativeModelsBudgetCertificate.budgetControlled,
      sampleNormalDerivativeModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleNormalDerivativeModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleNormalDerivativeModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleNormalDerivativeModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [NormalDerivativeModelsBudgetCertificate.controlled,
      sampleNormalDerivativeModelsBudgetCertificate]
  · norm_num [NormalDerivativeModelsBudgetCertificate.budgetControlled,
      sampleNormalDerivativeModelsBudgetCertificate]

example :
    sampleNormalDerivativeModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleNormalDerivativeModelsBudgetCertificate.size := by
  apply normalDerivativeModels_budgetCertificate_le_size
  constructor
  · norm_num [NormalDerivativeModelsBudgetCertificate.controlled,
      sampleNormalDerivativeModelsBudgetCertificate]
  · norm_num [NormalDerivativeModelsBudgetCertificate.budgetControlled,
      sampleNormalDerivativeModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List NormalDerivativeModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleNormalDerivativeModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleNormalDerivativeModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.NormalDerivativeModels
