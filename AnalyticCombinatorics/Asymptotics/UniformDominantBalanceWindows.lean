import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform dominant balance windows.

The finite schema records dominant scale, subordinate scale, and balance
slack.
-/

namespace AnalyticCombinatorics.Asymptotics.UniformDominantBalanceWindows

structure UniformDominantBalanceWindowData where
  dominantScale : ℕ
  subordinateScale : ℕ
  balanceSlack : ℕ
deriving DecidableEq, Repr

def dominantScalePositive (d : UniformDominantBalanceWindowData) : Prop :=
  0 < d.dominantScale

def subordinateControlled (d : UniformDominantBalanceWindowData) : Prop :=
  d.subordinateScale ≤ d.dominantScale + d.balanceSlack

def uniformDominantBalanceWindowReady
    (d : UniformDominantBalanceWindowData) : Prop :=
  dominantScalePositive d ∧ subordinateControlled d

def uniformDominantBalanceWindowBudget
    (d : UniformDominantBalanceWindowData) : ℕ :=
  d.dominantScale + d.subordinateScale + d.balanceSlack

theorem uniformDominantBalanceWindowReady.dominant
    {d : UniformDominantBalanceWindowData}
    (h : uniformDominantBalanceWindowReady d) :
    dominantScalePositive d ∧ subordinateControlled d ∧
      d.subordinateScale ≤ uniformDominantBalanceWindowBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold uniformDominantBalanceWindowBudget
  omega

theorem subordinateScale_le_dominantBalanceBudget
    (d : UniformDominantBalanceWindowData) :
    d.subordinateScale ≤ uniformDominantBalanceWindowBudget d := by
  unfold uniformDominantBalanceWindowBudget
  omega

def sampleUniformDominantBalanceWindowData :
    UniformDominantBalanceWindowData :=
  { dominantScale := 7, subordinateScale := 9, balanceSlack := 3 }

example :
    uniformDominantBalanceWindowReady
      sampleUniformDominantBalanceWindowData := by
  norm_num [uniformDominantBalanceWindowReady, dominantScalePositive]
  norm_num [subordinateControlled, sampleUniformDominantBalanceWindowData]

example :
    uniformDominantBalanceWindowBudget
      sampleUniformDominantBalanceWindowData = 19 := by
  native_decide

/-- Finite executable readiness audit for uniform dominant-balance data. -/
def uniformDominantBalanceDataListReady
    (data : List UniformDominantBalanceWindowData) : Bool :=
  data.all fun d =>
    0 < d.dominantScale && d.subordinateScale ≤ d.dominantScale + d.balanceSlack

theorem uniformDominantBalanceDataList_readyWindow :
    uniformDominantBalanceDataListReady
      [{ dominantScale := 4, subordinateScale := 5, balanceSlack := 1 },
       { dominantScale := 7, subordinateScale := 9, balanceSlack := 3 }] = true := by
  unfold uniformDominantBalanceDataListReady
  native_decide

/-- A certificate window for uniform dominant balance. -/
structure UniformDominantBalanceCertificateWindow where
  dominantWindow : ℕ
  subordinateWindow : ℕ
  balanceSlack : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- The subordinate window is controlled by the dominant window. -/
def uniformDominantBalanceCertificateControlled
    (w : UniformDominantBalanceCertificateWindow) : Prop :=
  w.subordinateWindow ≤ w.dominantWindow + w.balanceSlack + w.slack

/-- Readiness for a dominant balance certificate. -/
def uniformDominantBalanceCertificateReady
    (w : UniformDominantBalanceCertificateWindow) : Prop :=
  0 < w.dominantWindow ∧
    uniformDominantBalanceCertificateControlled w ∧
      w.certificateBudget ≤ w.dominantWindow + w.subordinateWindow + w.slack

/-- Total size of a dominant balance certificate. -/
def uniformDominantBalanceCertificate
    (w : UniformDominantBalanceCertificateWindow) : ℕ :=
  w.dominantWindow + w.subordinateWindow + w.balanceSlack +
    w.certificateBudget + w.slack

theorem uniformDominantBalanceCertificate_budget_le_certificate
    (w : UniformDominantBalanceCertificateWindow)
    (h : uniformDominantBalanceCertificateReady w) :
    w.certificateBudget ≤ uniformDominantBalanceCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold uniformDominantBalanceCertificate
  omega

def sampleUniformDominantBalanceCertificateWindow :
    UniformDominantBalanceCertificateWindow where
  dominantWindow := 7
  subordinateWindow := 8
  balanceSlack := 2
  certificateBudget := 14
  slack := 1

example :
    uniformDominantBalanceCertificateReady
      sampleUniformDominantBalanceCertificateWindow := by
  norm_num [uniformDominantBalanceCertificateReady,
    uniformDominantBalanceCertificateControlled,
    sampleUniformDominantBalanceCertificateWindow]

example :
    sampleUniformDominantBalanceCertificateWindow.certificateBudget ≤
      uniformDominantBalanceCertificate
        sampleUniformDominantBalanceCertificateWindow := by
  apply uniformDominantBalanceCertificate_budget_le_certificate
  norm_num [uniformDominantBalanceCertificateReady,
    uniformDominantBalanceCertificateControlled,
    sampleUniformDominantBalanceCertificateWindow]

structure UniformDominantBalanceRefinementCertificate where
  dominantWindow : ℕ
  subordinateWindow : ℕ
  balanceSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformDominantBalanceRefinementCertificate.subordinateControlled
    (c : UniformDominantBalanceRefinementCertificate) : Prop :=
  c.subordinateWindow ≤ c.dominantWindow + c.balanceSlackWindow + c.slack

def UniformDominantBalanceRefinementCertificate.certificateBudgetControlled
    (c : UniformDominantBalanceRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.dominantWindow + c.subordinateWindow + c.balanceSlackWindow + c.slack

def uniformDominantBalanceRefinementReady
    (c : UniformDominantBalanceRefinementCertificate) : Prop :=
  0 < c.dominantWindow ∧ c.subordinateControlled ∧ c.certificateBudgetControlled

def UniformDominantBalanceRefinementCertificate.size
    (c : UniformDominantBalanceRefinementCertificate) : ℕ :=
  c.dominantWindow + c.subordinateWindow + c.balanceSlackWindow + c.slack

theorem uniformDominantBalance_certificateBudgetWindow_le_size
    {c : UniformDominantBalanceRefinementCertificate}
    (h : uniformDominantBalanceRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleUniformDominantBalanceRefinementCertificate :
    UniformDominantBalanceRefinementCertificate :=
  { dominantWindow := 7, subordinateWindow := 8, balanceSlackWindow := 2,
    certificateBudgetWindow := 18, slack := 1 }

example : uniformDominantBalanceRefinementReady
    sampleUniformDominantBalanceRefinementCertificate := by
  norm_num [uniformDominantBalanceRefinementReady,
    UniformDominantBalanceRefinementCertificate.subordinateControlled,
    UniformDominantBalanceRefinementCertificate.certificateBudgetControlled,
    sampleUniformDominantBalanceRefinementCertificate]

example :
    sampleUniformDominantBalanceRefinementCertificate.certificateBudgetWindow ≤
      sampleUniformDominantBalanceRefinementCertificate.size := by
  norm_num [UniformDominantBalanceRefinementCertificate.size,
    sampleUniformDominantBalanceRefinementCertificate]

structure UniformDominantBalanceBudgetCertificate where
  dominantWindow : ℕ
  subordinateWindow : ℕ
  balanceSlackWindow : ℕ
  balanceBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformDominantBalanceBudgetCertificate.controlled
    (c : UniformDominantBalanceBudgetCertificate) : Prop :=
  0 < c.dominantWindow ∧
    c.subordinateWindow ≤ c.dominantWindow + c.balanceSlackWindow + c.slack ∧
      c.balanceBudgetWindow ≤
        c.dominantWindow + c.subordinateWindow + c.balanceSlackWindow + c.slack

def UniformDominantBalanceBudgetCertificate.budgetControlled
    (c : UniformDominantBalanceBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.dominantWindow + c.subordinateWindow + c.balanceSlackWindow +
      c.balanceBudgetWindow + c.slack

def UniformDominantBalanceBudgetCertificate.Ready
    (c : UniformDominantBalanceBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UniformDominantBalanceBudgetCertificate.size
    (c : UniformDominantBalanceBudgetCertificate) : ℕ :=
  c.dominantWindow + c.subordinateWindow + c.balanceSlackWindow +
    c.balanceBudgetWindow + c.slack

theorem uniformDominantBalance_budgetCertificate_le_size
    (c : UniformDominantBalanceBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformDominantBalanceBudgetCertificate :
    UniformDominantBalanceBudgetCertificate :=
  { dominantWindow := 7
    subordinateWindow := 8
    balanceSlackWindow := 2
    balanceBudgetWindow := 18
    certificateBudgetWindow := 36
    slack := 1 }

example : sampleUniformDominantBalanceBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformDominantBalanceBudgetCertificate.controlled,
      sampleUniformDominantBalanceBudgetCertificate]
  · norm_num [UniformDominantBalanceBudgetCertificate.budgetControlled,
      sampleUniformDominantBalanceBudgetCertificate]

example :
    sampleUniformDominantBalanceBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformDominantBalanceBudgetCertificate.size := by
  apply uniformDominantBalance_budgetCertificate_le_size
  constructor
  · norm_num [UniformDominantBalanceBudgetCertificate.controlled,
      sampleUniformDominantBalanceBudgetCertificate]
  · norm_num [UniformDominantBalanceBudgetCertificate.budgetControlled,
      sampleUniformDominantBalanceBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleUniformDominantBalanceBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformDominantBalanceBudgetCertificate.controlled,
      sampleUniformDominantBalanceBudgetCertificate]
  · norm_num [UniformDominantBalanceBudgetCertificate.budgetControlled,
      sampleUniformDominantBalanceBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformDominantBalanceBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformDominantBalanceBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List UniformDominantBalanceBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformDominantBalanceBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleUniformDominantBalanceBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.UniformDominantBalanceWindows
