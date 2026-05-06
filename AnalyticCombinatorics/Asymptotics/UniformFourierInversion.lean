import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform Fourier inversion.

The finite schema packages frequency cutoff, smoothness budget, and tail
budget for uniform Fourier inversion.
-/

namespace AnalyticCombinatorics.Asymptotics.UniformFourierInversion

structure UniformFourierInversionData where
  frequencyCutoff : ℕ
  smoothnessBudget : ℕ
  tailBudget : ℕ
deriving DecidableEq, Repr

def cutoffPositive (d : UniformFourierInversionData) : Prop :=
  0 < d.frequencyCutoff

def smoothnessControlled (d : UniformFourierInversionData) : Prop :=
  d.smoothnessBudget ≤ d.frequencyCutoff + d.tailBudget

def uniformFourierInversionReady
    (d : UniformFourierInversionData) : Prop :=
  cutoffPositive d ∧ smoothnessControlled d

def uniformFourierInversionBudget
    (d : UniformFourierInversionData) : ℕ :=
  d.frequencyCutoff + d.smoothnessBudget + d.tailBudget

theorem uniformFourierInversionReady.cutoff
    {d : UniformFourierInversionData}
    (h : uniformFourierInversionReady d) :
    cutoffPositive d ∧ smoothnessControlled d ∧
      d.smoothnessBudget ≤ uniformFourierInversionBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold uniformFourierInversionBudget
  omega

theorem smoothness_le_fourierInversionBudget
    (d : UniformFourierInversionData) :
    d.smoothnessBudget ≤ uniformFourierInversionBudget d := by
  unfold uniformFourierInversionBudget
  omega

def sampleUniformFourierInversionData : UniformFourierInversionData :=
  { frequencyCutoff := 8, smoothnessBudget := 10, tailBudget := 3 }

example : uniformFourierInversionReady sampleUniformFourierInversionData := by
  norm_num [uniformFourierInversionReady, cutoffPositive]
  norm_num [smoothnessControlled, sampleUniformFourierInversionData]

example :
    uniformFourierInversionBudget sampleUniformFourierInversionData = 21 := by
  native_decide

/-- Finite executable readiness audit for uniform Fourier inversion data. -/
def uniformFourierInversionDataListReady
    (data : List UniformFourierInversionData) : Bool :=
  data.all fun d =>
    0 < d.frequencyCutoff && d.smoothnessBudget ≤ d.frequencyCutoff + d.tailBudget

theorem uniformFourierInversionDataList_readyWindow :
    uniformFourierInversionDataListReady
      [{ frequencyCutoff := 4, smoothnessBudget := 5, tailBudget := 1 },
       { frequencyCutoff := 8, smoothnessBudget := 10, tailBudget := 3 }] = true := by
  unfold uniformFourierInversionDataListReady
  native_decide

/-- A certificate window for uniform Fourier inversion. -/
structure UniformFourierInversionCertificateWindow where
  cutoffWindow : ℕ
  smoothnessWindow : ℕ
  tailWindow : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- Smoothness is controlled by cutoff and tail budgets. -/
def uniformFourierInversionCertificateControlled
    (w : UniformFourierInversionCertificateWindow) : Prop :=
  w.smoothnessWindow ≤ w.cutoffWindow + w.tailWindow + w.slack

/-- Readiness for a Fourier inversion certificate. -/
def uniformFourierInversionCertificateReady
    (w : UniformFourierInversionCertificateWindow) : Prop :=
  0 < w.cutoffWindow ∧
    uniformFourierInversionCertificateControlled w ∧
      w.certificateBudget ≤ w.cutoffWindow + w.smoothnessWindow + w.slack

/-- Total size of a Fourier inversion certificate. -/
def uniformFourierInversionCertificate
    (w : UniformFourierInversionCertificateWindow) : ℕ :=
  w.cutoffWindow + w.smoothnessWindow + w.tailWindow + w.certificateBudget + w.slack

theorem uniformFourierInversionCertificate_budget_le_certificate
    (w : UniformFourierInversionCertificateWindow)
    (h : uniformFourierInversionCertificateReady w) :
    w.certificateBudget ≤ uniformFourierInversionCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold uniformFourierInversionCertificate
  omega

def sampleUniformFourierInversionCertificateWindow :
    UniformFourierInversionCertificateWindow where
  cutoffWindow := 8
  smoothnessWindow := 9
  tailWindow := 2
  certificateBudget := 16
  slack := 1

example :
    uniformFourierInversionCertificateReady
      sampleUniformFourierInversionCertificateWindow := by
  norm_num [uniformFourierInversionCertificateReady,
    uniformFourierInversionCertificateControlled,
    sampleUniformFourierInversionCertificateWindow]

example :
    sampleUniformFourierInversionCertificateWindow.certificateBudget ≤
      uniformFourierInversionCertificate
        sampleUniformFourierInversionCertificateWindow := by
  apply uniformFourierInversionCertificate_budget_le_certificate
  norm_num [uniformFourierInversionCertificateReady,
    uniformFourierInversionCertificateControlled,
    sampleUniformFourierInversionCertificateWindow]

structure UniformFourierInversionRefinementCertificate where
  cutoffWindow : ℕ
  smoothnessWindow : ℕ
  tailWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformFourierInversionRefinementCertificate.smoothnessControlled
    (c : UniformFourierInversionRefinementCertificate) : Prop :=
  c.smoothnessWindow ≤ c.cutoffWindow + c.tailWindow + c.slack

def UniformFourierInversionRefinementCertificate.certificateBudgetControlled
    (c : UniformFourierInversionRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.cutoffWindow + c.smoothnessWindow + c.tailWindow + c.slack

def uniformFourierInversionRefinementReady
    (c : UniformFourierInversionRefinementCertificate) : Prop :=
  0 < c.cutoffWindow ∧ c.smoothnessControlled ∧ c.certificateBudgetControlled

def UniformFourierInversionRefinementCertificate.size
    (c : UniformFourierInversionRefinementCertificate) : ℕ :=
  c.cutoffWindow + c.smoothnessWindow + c.tailWindow + c.slack

theorem uniformFourierInversion_certificateBudgetWindow_le_size
    {c : UniformFourierInversionRefinementCertificate}
    (h : uniformFourierInversionRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleUniformFourierInversionRefinementCertificate :
    UniformFourierInversionRefinementCertificate :=
  { cutoffWindow := 8, smoothnessWindow := 9, tailWindow := 2,
    certificateBudgetWindow := 20, slack := 1 }

example : uniformFourierInversionRefinementReady
    sampleUniformFourierInversionRefinementCertificate := by
  norm_num [uniformFourierInversionRefinementReady,
    UniformFourierInversionRefinementCertificate.smoothnessControlled,
    UniformFourierInversionRefinementCertificate.certificateBudgetControlled,
    sampleUniformFourierInversionRefinementCertificate]

example :
    sampleUniformFourierInversionRefinementCertificate.certificateBudgetWindow ≤
      sampleUniformFourierInversionRefinementCertificate.size := by
  norm_num [UniformFourierInversionRefinementCertificate.size,
    sampleUniformFourierInversionRefinementCertificate]

structure UniformFourierInversionBudgetCertificate where
  cutoffWindow : ℕ
  smoothnessWindow : ℕ
  tailWindow : ℕ
  inversionBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformFourierInversionBudgetCertificate.controlled
    (c : UniformFourierInversionBudgetCertificate) : Prop :=
  0 < c.cutoffWindow ∧
    c.smoothnessWindow ≤ c.cutoffWindow + c.tailWindow + c.slack ∧
      c.inversionBudgetWindow ≤
        c.cutoffWindow + c.smoothnessWindow + c.tailWindow + c.slack

def UniformFourierInversionBudgetCertificate.budgetControlled
    (c : UniformFourierInversionBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.cutoffWindow + c.smoothnessWindow + c.tailWindow +
      c.inversionBudgetWindow + c.slack

def UniformFourierInversionBudgetCertificate.Ready
    (c : UniformFourierInversionBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UniformFourierInversionBudgetCertificate.size
    (c : UniformFourierInversionBudgetCertificate) : ℕ :=
  c.cutoffWindow + c.smoothnessWindow + c.tailWindow +
    c.inversionBudgetWindow + c.slack

theorem uniformFourierInversion_budgetCertificate_le_size
    (c : UniformFourierInversionBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformFourierInversionBudgetCertificate :
    UniformFourierInversionBudgetCertificate :=
  { cutoffWindow := 8
    smoothnessWindow := 9
    tailWindow := 2
    inversionBudgetWindow := 20
    certificateBudgetWindow := 40
    slack := 1 }

example : sampleUniformFourierInversionBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformFourierInversionBudgetCertificate.controlled,
      sampleUniformFourierInversionBudgetCertificate]
  · norm_num [UniformFourierInversionBudgetCertificate.budgetControlled,
      sampleUniformFourierInversionBudgetCertificate]

example :
    sampleUniformFourierInversionBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformFourierInversionBudgetCertificate.size := by
  apply uniformFourierInversion_budgetCertificate_le_size
  constructor
  · norm_num [UniformFourierInversionBudgetCertificate.controlled,
      sampleUniformFourierInversionBudgetCertificate]
  · norm_num [UniformFourierInversionBudgetCertificate.budgetControlled,
      sampleUniformFourierInversionBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleUniformFourierInversionBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformFourierInversionBudgetCertificate.controlled,
      sampleUniformFourierInversionBudgetCertificate]
  · norm_num [UniformFourierInversionBudgetCertificate.budgetControlled,
      sampleUniformFourierInversionBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformFourierInversionBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformFourierInversionBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List UniformFourierInversionBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformFourierInversionBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleUniformFourierInversionBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.UniformFourierInversion
