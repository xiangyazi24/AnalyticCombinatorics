import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Pringsheim-style positivity schemas.

The analytic theorem is represented by positivity of coefficients and a
dominant positive-radius flag.
-/

namespace AnalyticCombinatorics.Asymptotics.PringsheimSchemas

structure PringsheimData where
  positiveCoefficients : Prop
  positiveRadius : Prop
  dominantBoundaryPoint : Prop
deriving Repr

def pringsheimReady (d : PringsheimData) : Prop :=
  d.positiveCoefficients ∧ d.positiveRadius ∧ d.dominantBoundaryPoint

def coefficientPrefixPositive (a : ℕ → ℕ) (N : ℕ) : Prop :=
  ∀ n, n ≤ N → 0 < a n

theorem pringsheimReady.radius {d : PringsheimData}
    (h : pringsheimReady d) :
    d.positiveRadius := h.2.1

theorem coefficientPrefixPositive_mono {a : ℕ → ℕ} {N M : ℕ}
    (h : coefficientPrefixPositive a M) (hNM : N ≤ M) :
    coefficientPrefixPositive a N := by
  intro n hn
  exact h n (le_trans hn hNM)

def samplePringsheim : PringsheimData :=
  { positiveCoefficients := coefficientPrefixPositive (fun _ : ℕ => 1) 5
    positiveRadius := 0 < 5
    dominantBoundaryPoint := 5 ≤ 5 }

example : pringsheimReady samplePringsheim := by
  unfold pringsheimReady samplePringsheim coefficientPrefixPositive
  constructor
  · intro n hn
    norm_num
  · norm_num

example : coefficientPrefixPositive (fun _ : ℕ => 1) 5 := by
  intro n hn
  norm_num

structure PringsheimWindow where
  coefficientPrefix : ℕ
  radiusBudget : ℕ
  boundaryCandidates : ℕ
  positivitySlack : ℕ
deriving DecidableEq, Repr

def PringsheimWindow.positiveReady (w : PringsheimWindow) : Prop :=
  0 < w.coefficientPrefix ∧ 0 < w.radiusBudget

def PringsheimWindow.boundaryControlled (w : PringsheimWindow) : Prop :=
  w.boundaryCandidates ≤ w.radiusBudget + w.positivitySlack

def PringsheimWindow.ready (w : PringsheimWindow) : Prop :=
  w.positiveReady ∧ w.boundaryControlled

def PringsheimWindow.certificate (w : PringsheimWindow) : ℕ :=
  w.coefficientPrefix + w.radiusBudget + w.boundaryCandidates + w.positivitySlack

theorem boundaryCandidates_le_certificate (w : PringsheimWindow) :
    w.boundaryCandidates ≤ w.certificate := by
  unfold PringsheimWindow.certificate
  omega

def samplePringsheimWindow : PringsheimWindow :=
  { coefficientPrefix := 5, radiusBudget := 5, boundaryCandidates := 1, positivitySlack := 0 }

example : samplePringsheimWindow.ready := by
  norm_num [samplePringsheimWindow, PringsheimWindow.ready,
    PringsheimWindow.positiveReady, PringsheimWindow.boundaryControlled]

/-- A refinement certificate for Pringsheim-style positivity windows. -/
structure PringsheimCertificate where
  coefficientPrefixWindow : ℕ
  radiusWindow : ℕ
  boundaryWindow : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- Positivity and boundary candidates are controlled by the radius window. -/
def pringsheimCertificateControlled
    (w : PringsheimCertificate) : Prop :=
  0 < w.coefficientPrefixWindow ∧
    0 < w.radiusWindow ∧
      w.boundaryWindow ≤ w.radiusWindow + w.slack

/-- Readiness for a Pringsheim certificate. -/
def pringsheimCertificateReady
    (w : PringsheimCertificate) : Prop :=
  pringsheimCertificateControlled w ∧
    w.certificateBudget ≤
      w.coefficientPrefixWindow + w.radiusWindow + w.boundaryWindow + w.slack

/-- Total size of a Pringsheim certificate. -/
def pringsheimCertificateSize (w : PringsheimCertificate) : ℕ :=
  w.coefficientPrefixWindow + w.radiusWindow + w.boundaryWindow +
    w.certificateBudget + w.slack

theorem pringsheimCertificate_budget_le_size
    (w : PringsheimCertificate)
    (h : pringsheimCertificateReady w) :
    w.certificateBudget ≤ pringsheimCertificateSize w := by
  rcases h with ⟨_, hbudget⟩
  unfold pringsheimCertificateSize
  omega

def samplePringsheimCertificate : PringsheimCertificate where
  coefficientPrefixWindow := 5
  radiusWindow := 5
  boundaryWindow := 1
  certificateBudget := 11
  slack := 0

example :
    pringsheimCertificateReady samplePringsheimCertificate := by
  norm_num [pringsheimCertificateReady,
    pringsheimCertificateControlled, samplePringsheimCertificate]

example :
    samplePringsheimCertificate.certificateBudget ≤
      pringsheimCertificateSize samplePringsheimCertificate := by
  apply pringsheimCertificate_budget_le_size
  norm_num [pringsheimCertificateReady,
    pringsheimCertificateControlled, samplePringsheimCertificate]

/-- A refinement certificate with the Pringsheim budget separated from size. -/
structure PringsheimRefinementCertificate where
  coefficientPrefixWindow : ℕ
  radiusWindow : ℕ
  boundaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ

def PringsheimRefinementCertificate.positivityControlled
    (cert : PringsheimRefinementCertificate) : Prop :=
  0 < cert.coefficientPrefixWindow ∧
    0 < cert.radiusWindow ∧
      cert.boundaryWindow ≤ cert.radiusWindow + cert.slack

def PringsheimRefinementCertificate.budgetControlled
    (cert : PringsheimRefinementCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.coefficientPrefixWindow + cert.radiusWindow + cert.boundaryWindow + cert.slack

def pringsheimRefinementReady
    (cert : PringsheimRefinementCertificate) : Prop :=
  cert.positivityControlled ∧ cert.budgetControlled

def PringsheimRefinementCertificate.size
    (cert : PringsheimRefinementCertificate) : ℕ :=
  cert.coefficientPrefixWindow + cert.radiusWindow + cert.boundaryWindow + cert.slack

theorem pringsheim_certificateBudgetWindow_le_size
    (cert : PringsheimRefinementCertificate)
    (h : pringsheimRefinementReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def samplePringsheimRefinementCertificate : PringsheimRefinementCertificate where
  coefficientPrefixWindow := 5
  radiusWindow := 5
  boundaryWindow := 1
  certificateBudgetWindow := 11
  slack := 0

example : pringsheimRefinementReady samplePringsheimRefinementCertificate := by
  norm_num [pringsheimRefinementReady,
    PringsheimRefinementCertificate.positivityControlled,
    PringsheimRefinementCertificate.budgetControlled,
    samplePringsheimRefinementCertificate]

example :
    samplePringsheimRefinementCertificate.certificateBudgetWindow ≤
      samplePringsheimRefinementCertificate.size := by
  apply pringsheim_certificateBudgetWindow_le_size
  norm_num [pringsheimRefinementReady,
    PringsheimRefinementCertificate.positivityControlled,
    PringsheimRefinementCertificate.budgetControlled,
    samplePringsheimRefinementCertificate]


structure PringsheimSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PringsheimSchemasBudgetCertificate.controlled
    (c : PringsheimSchemasBudgetCertificate) : Prop :=
  0 < c.primaryWindow ∧ c.secondaryWindow ≤ c.primaryWindow + c.slack

def PringsheimSchemasBudgetCertificate.budgetControlled
    (c : PringsheimSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def PringsheimSchemasBudgetCertificate.Ready
    (c : PringsheimSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PringsheimSchemasBudgetCertificate.size
    (c : PringsheimSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem pringsheimSchemas_budgetCertificate_le_size
    (c : PringsheimSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def samplePringsheimSchemasBudgetCertificate :
    PringsheimSchemasBudgetCertificate :=
  { primaryWindow := 5
    secondaryWindow := 6
    certificateBudgetWindow := 12
    slack := 1 }

example : samplePringsheimSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [PringsheimSchemasBudgetCertificate.controlled,
      samplePringsheimSchemasBudgetCertificate]
  · norm_num [PringsheimSchemasBudgetCertificate.budgetControlled,
      samplePringsheimSchemasBudgetCertificate]

example :
    samplePringsheimSchemasBudgetCertificate.certificateBudgetWindow ≤
      samplePringsheimSchemasBudgetCertificate.size := by
  apply pringsheimSchemas_budgetCertificate_le_size
  constructor
  · norm_num [PringsheimSchemasBudgetCertificate.controlled,
      samplePringsheimSchemasBudgetCertificate]
  · norm_num [PringsheimSchemasBudgetCertificate.budgetControlled,
      samplePringsheimSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    samplePringsheimSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [PringsheimSchemasBudgetCertificate.controlled,
      samplePringsheimSchemasBudgetCertificate]
  · norm_num [PringsheimSchemasBudgetCertificate.budgetControlled,
      samplePringsheimSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    samplePringsheimSchemasBudgetCertificate.certificateBudgetWindow ≤
      samplePringsheimSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List PringsheimSchemasBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [samplePringsheimSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady samplePringsheimSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.Asymptotics.PringsheimSchemas
