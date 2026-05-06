import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Periodic fluctuation law bookkeeping.

The finite schema records the period, amplitude budget, and centering
condition for oscillating terms in universal laws.
-/

namespace AnalyticCombinatorics.AppC.PeriodicFluctuationLaws

def periodicWith (period : ℕ) (f : ℕ → ℕ) : Prop :=
  ∀ n, f (n + period) = f n

structure FluctuationLaw where
  period : ℕ
  amplitudeBudget : ℕ
  centered : Prop

def fluctuationReady (law : FluctuationLaw) : Prop :=
  0 < law.period ∧ law.centered

def constantPhase (c : ℕ) (n : ℕ) : ℕ := c + (n - n)

theorem constantPhase_periodic (period c : ℕ) :
    periodicWith period (constantPhase c) := by
  intro n
  simp [constantPhase]

theorem fluctuationReady.centered {law : FluctuationLaw}
    (h : fluctuationReady law) :
    law.centered := by
  rcases h with ⟨hleft, hright⟩
  exact hright

def sampleFluctuation : FluctuationLaw :=
  { period := 3, amplitudeBudget := 5, centered := 0 ≤ 5 }

example : fluctuationReady sampleFluctuation := by
  norm_num [fluctuationReady, sampleFluctuation]

example : periodicWith 7 (constantPhase 4) := by
  exact constantPhase_periodic 7 4

structure FluctuationWindow where
  period : ℕ
  amplitudeBudget : ℕ
  centeredMass : ℕ
  phaseSlack : ℕ
deriving DecidableEq, Repr

def FluctuationWindow.periodReady (w : FluctuationWindow) : Prop :=
  0 < w.period

def FluctuationWindow.centeredControlled (w : FluctuationWindow) : Prop :=
  w.centeredMass ≤ w.amplitudeBudget + w.phaseSlack

def FluctuationWindow.ready (w : FluctuationWindow) : Prop :=
  w.periodReady ∧ w.centeredControlled

def FluctuationWindow.certificate (w : FluctuationWindow) : ℕ :=
  w.period + w.amplitudeBudget + w.centeredMass + w.phaseSlack

theorem centeredMass_le_certificate (w : FluctuationWindow) :
    w.centeredMass ≤ w.certificate := by
  unfold FluctuationWindow.certificate
  omega

def sampleFluctuationWindow : FluctuationWindow :=
  { period := 3, amplitudeBudget := 5, centeredMass := 2, phaseSlack := 0 }

example : sampleFluctuationWindow.ready := by
  norm_num [sampleFluctuationWindow, FluctuationWindow.ready,
    FluctuationWindow.periodReady, FluctuationWindow.centeredControlled]

structure FluctuationRefinementWindow where
  periodWindow : ℕ
  amplitudeWindow : ℕ
  centeredWindow : ℕ
  fluctuationBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FluctuationRefinementWindow.centeredControlled
    (w : FluctuationRefinementWindow) : Prop :=
  w.centeredWindow ≤ w.amplitudeWindow + w.slack

def fluctuationRefinementWindowReady (w : FluctuationRefinementWindow) : Prop :=
  0 < w.periodWindow ∧ w.centeredControlled ∧
    w.fluctuationBudget ≤ w.periodWindow + w.amplitudeWindow + w.centeredWindow + w.slack

def FluctuationRefinementWindow.certificate
    (w : FluctuationRefinementWindow) : ℕ :=
  w.periodWindow + w.amplitudeWindow + w.centeredWindow + w.fluctuationBudget + w.slack

theorem fluctuationRefinement_budget_le_certificate
    (w : FluctuationRefinementWindow) :
    w.fluctuationBudget ≤ w.certificate := by
  unfold FluctuationRefinementWindow.certificate
  omega

def sampleFluctuationRefinementWindow : FluctuationRefinementWindow :=
  { periodWindow := 3, amplitudeWindow := 5, centeredWindow := 2,
    fluctuationBudget := 11, slack := 1 }

example : fluctuationRefinementWindowReady sampleFluctuationRefinementWindow := by
  norm_num [fluctuationRefinementWindowReady,
    FluctuationRefinementWindow.centeredControlled, sampleFluctuationRefinementWindow]


structure PeriodicFluctuationLawsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PeriodicFluctuationLawsBudgetCertificate.controlled
    (c : PeriodicFluctuationLawsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def PeriodicFluctuationLawsBudgetCertificate.budgetControlled
    (c : PeriodicFluctuationLawsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def PeriodicFluctuationLawsBudgetCertificate.Ready
    (c : PeriodicFluctuationLawsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PeriodicFluctuationLawsBudgetCertificate.size
    (c : PeriodicFluctuationLawsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem periodicFluctuationLaws_budgetCertificate_le_size
    (c : PeriodicFluctuationLawsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def samplePeriodicFluctuationLawsBudgetCertificate :
    PeriodicFluctuationLawsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : samplePeriodicFluctuationLawsBudgetCertificate.Ready := by
  constructor
  · norm_num [PeriodicFluctuationLawsBudgetCertificate.controlled,
      samplePeriodicFluctuationLawsBudgetCertificate]
  · norm_num [PeriodicFluctuationLawsBudgetCertificate.budgetControlled,
      samplePeriodicFluctuationLawsBudgetCertificate]

example :
    samplePeriodicFluctuationLawsBudgetCertificate.certificateBudgetWindow ≤
      samplePeriodicFluctuationLawsBudgetCertificate.size := by
  apply periodicFluctuationLaws_budgetCertificate_le_size
  constructor
  · norm_num [PeriodicFluctuationLawsBudgetCertificate.controlled,
      samplePeriodicFluctuationLawsBudgetCertificate]
  · norm_num [PeriodicFluctuationLawsBudgetCertificate.budgetControlled,
      samplePeriodicFluctuationLawsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    samplePeriodicFluctuationLawsBudgetCertificate.Ready := by
  constructor
  · norm_num [PeriodicFluctuationLawsBudgetCertificate.controlled,
      samplePeriodicFluctuationLawsBudgetCertificate]
  · norm_num [PeriodicFluctuationLawsBudgetCertificate.budgetControlled,
      samplePeriodicFluctuationLawsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    samplePeriodicFluctuationLawsBudgetCertificate.certificateBudgetWindow ≤
      samplePeriodicFluctuationLawsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List PeriodicFluctuationLawsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [samplePeriodicFluctuationLawsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady samplePeriodicFluctuationLawsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.PeriodicFluctuationLaws
