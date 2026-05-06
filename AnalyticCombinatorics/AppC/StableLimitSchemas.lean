import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Stable limit schemas.

The finite record packages scale, skewness, and tail budgets for stable
limit templates.
-/

namespace AnalyticCombinatorics.AppC.StableLimitSchemas

structure StableLimitData where
  scaleBudget : ℕ
  skewnessBudget : ℕ
  tailBudget : ℕ
deriving DecidableEq, Repr

def scalePositive (d : StableLimitData) : Prop :=
  0 < d.scaleBudget

def skewnessControlled (d : StableLimitData) : Prop :=
  d.skewnessBudget ≤ d.scaleBudget + d.tailBudget

def stableLimitReady (d : StableLimitData) : Prop :=
  scalePositive d ∧ skewnessControlled d

def stableLimitBudget (d : StableLimitData) : ℕ :=
  d.scaleBudget + d.skewnessBudget + d.tailBudget

theorem stableLimitReady.scale {d : StableLimitData}
    (h : stableLimitReady d) :
    scalePositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem skewnessBudget_le_stableBudget (d : StableLimitData) :
    d.skewnessBudget ≤ stableLimitBudget d := by
  unfold stableLimitBudget
  omega

def sampleStableLimitData : StableLimitData :=
  { scaleBudget := 8, skewnessBudget := 10, tailBudget := 3 }

example : stableLimitReady sampleStableLimitData := by
  norm_num [stableLimitReady, scalePositive]
  norm_num [skewnessControlled, sampleStableLimitData]

example : stableLimitBudget sampleStableLimitData = 21 := by
  native_decide

structure StableLimitWindow where
  scaleBudget : ℕ
  skewnessBudget : ℕ
  tailBudget : ℕ
  normalizationBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def StableLimitWindow.skewnessControlled (w : StableLimitWindow) : Prop :=
  w.skewnessBudget ≤ w.scaleBudget + w.tailBudget + w.slack

def StableLimitWindow.normalizationControlled (w : StableLimitWindow) : Prop :=
  w.normalizationBudget ≤ w.scaleBudget + w.skewnessBudget + w.tailBudget + w.slack

def stableLimitWindowReady (w : StableLimitWindow) : Prop :=
  0 < w.scaleBudget ∧
    w.skewnessControlled ∧
    w.normalizationControlled

def StableLimitWindow.certificate (w : StableLimitWindow) : ℕ :=
  w.scaleBudget + w.skewnessBudget + w.tailBudget + w.slack

theorem stableLimit_normalizationBudget_le_certificate {w : StableLimitWindow}
    (h : stableLimitWindowReady w) :
    w.normalizationBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hnorm⟩
  exact hnorm

def sampleStableLimitWindow : StableLimitWindow :=
  { scaleBudget := 8, skewnessBudget := 10, tailBudget := 3, normalizationBudget := 20,
    slack := 0 }

example : stableLimitWindowReady sampleStableLimitWindow := by
  norm_num [stableLimitWindowReady, StableLimitWindow.skewnessControlled,
    StableLimitWindow.normalizationControlled, sampleStableLimitWindow]

example : sampleStableLimitWindow.certificate = 21 := by
  native_decide


structure StableLimitSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def StableLimitSchemasBudgetCertificate.controlled
    (c : StableLimitSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def StableLimitSchemasBudgetCertificate.budgetControlled
    (c : StableLimitSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def StableLimitSchemasBudgetCertificate.Ready
    (c : StableLimitSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def StableLimitSchemasBudgetCertificate.size
    (c : StableLimitSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem stableLimitSchemas_budgetCertificate_le_size
    (c : StableLimitSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleStableLimitSchemasBudgetCertificate :
    StableLimitSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleStableLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [StableLimitSchemasBudgetCertificate.controlled,
      sampleStableLimitSchemasBudgetCertificate]
  · norm_num [StableLimitSchemasBudgetCertificate.budgetControlled,
      sampleStableLimitSchemasBudgetCertificate]

example : sampleStableLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [StableLimitSchemasBudgetCertificate.controlled,
      sampleStableLimitSchemasBudgetCertificate]
  · norm_num [StableLimitSchemasBudgetCertificate.budgetControlled,
      sampleStableLimitSchemasBudgetCertificate]

example :
    sampleStableLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleStableLimitSchemasBudgetCertificate.size := by
  apply stableLimitSchemas_budgetCertificate_le_size
  constructor
  · norm_num [StableLimitSchemasBudgetCertificate.controlled,
      sampleStableLimitSchemasBudgetCertificate]
  · norm_num [StableLimitSchemasBudgetCertificate.budgetControlled,
      sampleStableLimitSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleStableLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleStableLimitSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List StableLimitSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleStableLimitSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleStableLimitSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.StableLimitSchemas
