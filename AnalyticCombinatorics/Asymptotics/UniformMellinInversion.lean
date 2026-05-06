import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform Mellin inversion.

The finite schema records strip width, vertical cutoff, and error budget
for uniform Mellin inversion estimates.
-/

namespace AnalyticCombinatorics.Asymptotics.UniformMellinInversion

structure UniformMellinInversionData where
  stripWidth : ℕ
  verticalCutoff : ℕ
  errorBudget : ℕ
deriving DecidableEq, Repr

def positiveStripWidth (d : UniformMellinInversionData) : Prop :=
  0 < d.stripWidth

def cutoffControlled (d : UniformMellinInversionData) : Prop :=
  d.verticalCutoff ≤ d.stripWidth + d.errorBudget

def uniformMellinInversionReady (d : UniformMellinInversionData) : Prop :=
  positiveStripWidth d ∧ cutoffControlled d

def uniformMellinInversionBudget (d : UniformMellinInversionData) : ℕ :=
  d.stripWidth + d.verticalCutoff + d.errorBudget

theorem uniformMellinInversionReady.strip
    {d : UniformMellinInversionData}
    (h : uniformMellinInversionReady d) :
    positiveStripWidth d ∧ cutoffControlled d ∧
      d.verticalCutoff ≤ uniformMellinInversionBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold uniformMellinInversionBudget
  omega

theorem cutoff_le_mellinInversionBudget
    (d : UniformMellinInversionData) :
    d.verticalCutoff ≤ uniformMellinInversionBudget d := by
  unfold uniformMellinInversionBudget
  omega

def sampleUniformMellinInversionData : UniformMellinInversionData :=
  { stripWidth := 5, verticalCutoff := 8, errorBudget := 4 }

example : uniformMellinInversionReady sampleUniformMellinInversionData := by
  norm_num [uniformMellinInversionReady, positiveStripWidth]
  norm_num [cutoffControlled, sampleUniformMellinInversionData]

example : uniformMellinInversionBudget sampleUniformMellinInversionData = 17 := by
  native_decide

/-- Finite executable readiness audit for uniform Mellin inversion data. -/
def uniformMellinInversionDataListReady
    (data : List UniformMellinInversionData) : Bool :=
  data.all fun d =>
    0 < d.stripWidth && d.verticalCutoff ≤ d.stripWidth + d.errorBudget

theorem uniformMellinInversionDataList_readyWindow :
    uniformMellinInversionDataListReady
      [{ stripWidth := 4, verticalCutoff := 5, errorBudget := 1 },
       { stripWidth := 5, verticalCutoff := 8, errorBudget := 4 }] = true := by
  unfold uniformMellinInversionDataListReady
  native_decide

/-- A certificate window for uniform Mellin inversion. -/
structure UniformMellinInversionCertificateWindow where
  stripWindow : ℕ
  cutoffWindow : ℕ
  errorWindow : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- The cutoff window is controlled by strip width and error. -/
def uniformMellinInversionCertificateControlled
    (w : UniformMellinInversionCertificateWindow) : Prop :=
  w.cutoffWindow ≤ w.stripWindow + w.errorWindow + w.slack

/-- Readiness for a Mellin inversion certificate. -/
def uniformMellinInversionCertificateReady
    (w : UniformMellinInversionCertificateWindow) : Prop :=
  0 < w.stripWindow ∧
    uniformMellinInversionCertificateControlled w ∧
      w.certificateBudget ≤ w.stripWindow + w.cutoffWindow + w.slack

/-- Total size of a Mellin inversion certificate. -/
def uniformMellinInversionCertificate
    (w : UniformMellinInversionCertificateWindow) : ℕ :=
  w.stripWindow + w.cutoffWindow + w.errorWindow + w.certificateBudget + w.slack

theorem uniformMellinInversionCertificate_budget_le_certificate
    (w : UniformMellinInversionCertificateWindow)
    (h : uniformMellinInversionCertificateReady w) :
    w.certificateBudget ≤ uniformMellinInversionCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold uniformMellinInversionCertificate
  omega

def sampleUniformMellinInversionCertificateWindow :
    UniformMellinInversionCertificateWindow where
  stripWindow := 6
  cutoffWindow := 7
  errorWindow := 2
  certificateBudget := 12
  slack := 1

example :
    uniformMellinInversionCertificateReady
      sampleUniformMellinInversionCertificateWindow := by
  norm_num [uniformMellinInversionCertificateReady,
    uniformMellinInversionCertificateControlled,
    sampleUniformMellinInversionCertificateWindow]

example :
    sampleUniformMellinInversionCertificateWindow.certificateBudget ≤
      uniformMellinInversionCertificate
        sampleUniformMellinInversionCertificateWindow := by
  apply uniformMellinInversionCertificate_budget_le_certificate
  norm_num [uniformMellinInversionCertificateReady,
    uniformMellinInversionCertificateControlled,
    sampleUniformMellinInversionCertificateWindow]

structure UniformMellinInversionRefinementCertificate where
  stripWindow : ℕ
  cutoffWindow : ℕ
  errorWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformMellinInversionRefinementCertificate.cutoffControlled
    (c : UniformMellinInversionRefinementCertificate) : Prop :=
  c.cutoffWindow ≤ c.stripWindow + c.errorWindow + c.slack

def UniformMellinInversionRefinementCertificate.certificateBudgetControlled
    (c : UniformMellinInversionRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.stripWindow + c.cutoffWindow + c.errorWindow + c.slack

def uniformMellinInversionRefinementReady
    (c : UniformMellinInversionRefinementCertificate) : Prop :=
  0 < c.stripWindow ∧ c.cutoffControlled ∧ c.certificateBudgetControlled

def UniformMellinInversionRefinementCertificate.size
    (c : UniformMellinInversionRefinementCertificate) : ℕ :=
  c.stripWindow + c.cutoffWindow + c.errorWindow + c.slack

theorem uniformMellinInversion_certificateBudgetWindow_le_size
    {c : UniformMellinInversionRefinementCertificate}
    (h : uniformMellinInversionRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleUniformMellinInversionRefinementCertificate :
    UniformMellinInversionRefinementCertificate :=
  { stripWindow := 6, cutoffWindow := 7, errorWindow := 2,
    certificateBudgetWindow := 16, slack := 1 }

example : uniformMellinInversionRefinementReady
    sampleUniformMellinInversionRefinementCertificate := by
  norm_num [uniformMellinInversionRefinementReady,
    UniformMellinInversionRefinementCertificate.cutoffControlled,
    UniformMellinInversionRefinementCertificate.certificateBudgetControlled,
    sampleUniformMellinInversionRefinementCertificate]

example :
    sampleUniformMellinInversionRefinementCertificate.certificateBudgetWindow ≤
      sampleUniformMellinInversionRefinementCertificate.size := by
  norm_num [UniformMellinInversionRefinementCertificate.size,
    sampleUniformMellinInversionRefinementCertificate]

structure UniformMellinInversionBudgetCertificate where
  stripWindow : ℕ
  cutoffWindow : ℕ
  errorWindow : ℕ
  cutoffBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformMellinInversionBudgetCertificate.controlled
    (c : UniformMellinInversionBudgetCertificate) : Prop :=
  0 < c.stripWindow ∧
    c.cutoffWindow ≤ c.stripWindow + c.errorWindow + c.slack ∧
      c.cutoffBudgetWindow ≤
        c.stripWindow + c.cutoffWindow + c.errorWindow + c.slack

def UniformMellinInversionBudgetCertificate.budgetControlled
    (c : UniformMellinInversionBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.stripWindow + c.cutoffWindow + c.errorWindow +
      c.cutoffBudgetWindow + c.slack

def UniformMellinInversionBudgetCertificate.Ready
    (c : UniformMellinInversionBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UniformMellinInversionBudgetCertificate.size
    (c : UniformMellinInversionBudgetCertificate) : ℕ :=
  c.stripWindow + c.cutoffWindow + c.errorWindow +
    c.cutoffBudgetWindow + c.slack

theorem uniformMellinInversion_budgetCertificate_le_size
    (c : UniformMellinInversionBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformMellinInversionBudgetCertificate :
    UniformMellinInversionBudgetCertificate :=
  { stripWindow := 6
    cutoffWindow := 7
    errorWindow := 2
    cutoffBudgetWindow := 16
    certificateBudgetWindow := 32
    slack := 1 }

example : sampleUniformMellinInversionBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformMellinInversionBudgetCertificate.controlled,
      sampleUniformMellinInversionBudgetCertificate]
  · norm_num [UniformMellinInversionBudgetCertificate.budgetControlled,
      sampleUniformMellinInversionBudgetCertificate]

example :
    sampleUniformMellinInversionBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformMellinInversionBudgetCertificate.size := by
  apply uniformMellinInversion_budgetCertificate_le_size
  constructor
  · norm_num [UniformMellinInversionBudgetCertificate.controlled,
      sampleUniformMellinInversionBudgetCertificate]
  · norm_num [UniformMellinInversionBudgetCertificate.budgetControlled,
      sampleUniformMellinInversionBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleUniformMellinInversionBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformMellinInversionBudgetCertificate.controlled,
      sampleUniformMellinInversionBudgetCertificate]
  · norm_num [UniformMellinInversionBudgetCertificate.budgetControlled,
      sampleUniformMellinInversionBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformMellinInversionBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformMellinInversionBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List UniformMellinInversionBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformMellinInversionBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleUniformMellinInversionBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.UniformMellinInversion
