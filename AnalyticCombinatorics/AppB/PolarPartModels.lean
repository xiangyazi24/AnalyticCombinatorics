import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Polar-part bookkeeping models.

The finite data records pole order, principal mass, and regular remainder.
-/

namespace AnalyticCombinatorics.AppB.PolarPartModels

structure PolarPartDatum where
  poleOrder : ℕ
  principalMass : ℕ
  regularRemainder : ℕ
deriving DecidableEq, Repr

def positivePoleOrder (d : PolarPartDatum) : Prop :=
  0 < d.poleOrder

def polarPartControlled (d : PolarPartDatum) : Prop :=
  d.principalMass ≤ d.poleOrder + d.regularRemainder

def polarPartReady (d : PolarPartDatum) : Prop :=
  positivePoleOrder d ∧ polarPartControlled d

def polarBudget (d : PolarPartDatum) : ℕ :=
  d.poleOrder + d.principalMass + d.regularRemainder

theorem polarPartReady.controlled {d : PolarPartDatum}
    (h : polarPartReady d) :
    positivePoleOrder d ∧ polarPartControlled d ∧
      d.poleOrder ≤ polarBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold polarBudget
  omega

theorem poleOrder_le_polarBudget (d : PolarPartDatum) :
    d.poleOrder ≤ polarBudget d := by
  unfold polarBudget
  omega

def samplePolarPart : PolarPartDatum :=
  { poleOrder := 3, principalMass := 5, regularRemainder := 4 }

example : polarPartReady samplePolarPart := by
  norm_num [polarPartReady, positivePoleOrder, polarPartControlled, samplePolarPart]

example : polarBudget samplePolarPart = 12 := by
  native_decide

structure PolarPartWindow where
  poleOrder : ℕ
  principalMass : ℕ
  regularRemainder : ℕ
  extractionBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PolarPartWindow.principalControlled (w : PolarPartWindow) : Prop :=
  w.principalMass ≤ w.poleOrder + w.regularRemainder + w.slack

def PolarPartWindow.extractionControlled (w : PolarPartWindow) : Prop :=
  w.extractionBudget ≤ w.poleOrder + w.principalMass + w.regularRemainder + w.slack

def polarPartWindowReady (w : PolarPartWindow) : Prop :=
  0 < w.poleOrder ∧
    w.principalControlled ∧
    w.extractionControlled

def PolarPartWindow.certificate (w : PolarPartWindow) : ℕ :=
  w.poleOrder + w.principalMass + w.regularRemainder + w.slack

theorem polarPart_extractionBudget_le_certificate {w : PolarPartWindow}
    (h : polarPartWindowReady w) :
    w.extractionBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hextract⟩
  exact hextract

def samplePolarPartWindow : PolarPartWindow :=
  { poleOrder := 3, principalMass := 5, regularRemainder := 4, extractionBudget := 11,
    slack := 0 }

example : polarPartWindowReady samplePolarPartWindow := by
  norm_num [polarPartWindowReady, PolarPartWindow.principalControlled,
    PolarPartWindow.extractionControlled, samplePolarPartWindow]

example : samplePolarPartWindow.certificate = 12 := by
  native_decide


structure PolarPartModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PolarPartModelsBudgetCertificate.controlled
    (c : PolarPartModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def PolarPartModelsBudgetCertificate.budgetControlled
    (c : PolarPartModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def PolarPartModelsBudgetCertificate.Ready
    (c : PolarPartModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PolarPartModelsBudgetCertificate.size
    (c : PolarPartModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem polarPartModels_budgetCertificate_le_size
    (c : PolarPartModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def samplePolarPartModelsBudgetCertificate :
    PolarPartModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    samplePolarPartModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [PolarPartModelsBudgetCertificate.controlled,
      samplePolarPartModelsBudgetCertificate]
  · norm_num [PolarPartModelsBudgetCertificate.budgetControlled,
      samplePolarPartModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    samplePolarPartModelsBudgetCertificate.certificateBudgetWindow ≤
      samplePolarPartModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : samplePolarPartModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [PolarPartModelsBudgetCertificate.controlled,
      samplePolarPartModelsBudgetCertificate]
  · norm_num [PolarPartModelsBudgetCertificate.budgetControlled,
      samplePolarPartModelsBudgetCertificate]

example :
    samplePolarPartModelsBudgetCertificate.certificateBudgetWindow ≤
      samplePolarPartModelsBudgetCertificate.size := by
  apply polarPartModels_budgetCertificate_le_size
  constructor
  · norm_num [PolarPartModelsBudgetCertificate.controlled,
      samplePolarPartModelsBudgetCertificate]
  · norm_num [PolarPartModelsBudgetCertificate.budgetControlled,
      samplePolarPartModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List PolarPartModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [samplePolarPartModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady samplePolarPartModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.PolarPartModels
