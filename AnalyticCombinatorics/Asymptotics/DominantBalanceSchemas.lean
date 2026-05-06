import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Dominant-balance schema bookkeeping.

The data records which term dominates and how much slack remains after
absorbing lower-order contributions.
-/

namespace AnalyticCombinatorics.Asymptotics.DominantBalanceSchemas

structure BalanceData where
  dominantTerm : ℕ
  lowerOrderTerm : ℕ
  errorTerm : ℕ
deriving DecidableEq, Repr

def lowerOrderAbsorbed (d : BalanceData) : Prop :=
  d.lowerOrderTerm + d.errorTerm ≤ d.dominantTerm

def balanceSlack (d : BalanceData) : ℕ :=
  d.dominantTerm - (d.lowerOrderTerm + d.errorTerm)

def dominantPositive (d : BalanceData) : Prop :=
  0 < d.dominantTerm

def balanceReady (d : BalanceData) : Prop :=
  dominantPositive d ∧ lowerOrderAbsorbed d

theorem lowerOrderAbsorbed.lower_le {d : BalanceData}
    (h : lowerOrderAbsorbed d) :
    d.lowerOrderTerm ≤ d.dominantTerm := by
  unfold lowerOrderAbsorbed at h
  omega

theorem balanceReady.absorbed {d : BalanceData}
    (h : balanceReady d) :
    dominantPositive d ∧ lowerOrderAbsorbed d ∧ d.lowerOrderTerm ≤ d.dominantTerm := by
  refine ⟨h.1, h.2, ?_⟩
  exact lowerOrderAbsorbed.lower_le h.2

def sampleBalance : BalanceData :=
  { dominantTerm := 12, lowerOrderTerm := 5, errorTerm := 3 }

example : balanceReady sampleBalance := by
  norm_num [balanceReady, dominantPositive, lowerOrderAbsorbed, sampleBalance]

example : balanceSlack sampleBalance = 4 := by
  native_decide

/-- Finite executable readiness audit for dominant-balance data. -/
def balanceDataListReady (data : List BalanceData) : Bool :=
  data.all fun d =>
    0 < d.dominantTerm && d.lowerOrderTerm + d.errorTerm ≤ d.dominantTerm

theorem balanceDataList_readyWindow :
    balanceDataListReady
      [{ dominantTerm := 8, lowerOrderTerm := 3, errorTerm := 2 },
       { dominantTerm := 12, lowerOrderTerm := 5, errorTerm := 3 }] = true := by
  unfold balanceDataListReady
  native_decide

structure DominantBalanceWindow where
  dominantTerm : ℕ
  lowerOrderTerm : ℕ
  errorTerm : ℕ
  comparisonBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DominantBalanceWindow.absorbed (w : DominantBalanceWindow) : Prop :=
  w.lowerOrderTerm + w.errorTerm ≤ w.dominantTerm + w.slack

def DominantBalanceWindow.comparisonControlled (w : DominantBalanceWindow) : Prop :=
  w.comparisonBudget ≤ w.dominantTerm + w.lowerOrderTerm + w.errorTerm + w.slack

def dominantBalanceWindowReady (w : DominantBalanceWindow) : Prop :=
  0 < w.dominantTerm ∧
    w.absorbed ∧
    w.comparisonControlled

def DominantBalanceWindow.certificate (w : DominantBalanceWindow) : ℕ :=
  w.dominantTerm + w.lowerOrderTerm + w.errorTerm + w.slack

theorem dominantBalance_comparisonBudget_le_certificate {w : DominantBalanceWindow}
    (h : dominantBalanceWindowReady w) :
    w.comparisonBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hcomparison⟩
  exact hcomparison

def sampleDominantBalanceWindow : DominantBalanceWindow :=
  { dominantTerm := 12, lowerOrderTerm := 5, errorTerm := 3, comparisonBudget := 19,
    slack := 0 }

example : dominantBalanceWindowReady sampleDominantBalanceWindow := by
  norm_num [dominantBalanceWindowReady, DominantBalanceWindow.absorbed,
    DominantBalanceWindow.comparisonControlled, sampleDominantBalanceWindow]

example : sampleDominantBalanceWindow.certificate = 20 := by
  native_decide

structure DominantBalanceCertificate where
  dominantWindow : ℕ
  lowerWindow : ℕ
  errorWindow : ℕ
  comparisonWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DominantBalanceCertificate.balanceControlled
    (c : DominantBalanceCertificate) : Prop :=
  c.lowerWindow + c.errorWindow ≤ c.dominantWindow + c.slack

def DominantBalanceCertificate.comparisonControlled
    (c : DominantBalanceCertificate) : Prop :=
  c.comparisonWindow ≤ c.dominantWindow + c.lowerWindow + c.errorWindow + c.slack

def dominantBalanceCertificateReady
    (c : DominantBalanceCertificate) : Prop :=
  0 < c.dominantWindow ∧ c.balanceControlled ∧ c.comparisonControlled

def DominantBalanceCertificate.size
    (c : DominantBalanceCertificate) : ℕ :=
  c.dominantWindow + c.lowerWindow + c.errorWindow + c.slack

theorem dominantBalance_comparisonWindow_le_size
    {c : DominantBalanceCertificate}
    (h : dominantBalanceCertificateReady c) :
    c.comparisonWindow ≤ c.size := by
  rcases h with ⟨_, _, hcomparison⟩
  exact hcomparison

def sampleDominantBalanceCertificate : DominantBalanceCertificate :=
  { dominantWindow := 14, lowerWindow := 5, errorWindow := 3,
    comparisonWindow := 21, slack := 1 }

example : dominantBalanceCertificateReady sampleDominantBalanceCertificate := by
  norm_num [dominantBalanceCertificateReady,
    DominantBalanceCertificate.balanceControlled,
    DominantBalanceCertificate.comparisonControlled,
    sampleDominantBalanceCertificate]

example :
    sampleDominantBalanceCertificate.comparisonWindow ≤
      sampleDominantBalanceCertificate.size := by
  norm_num [DominantBalanceCertificate.size, sampleDominantBalanceCertificate]

/-- A refinement certificate with the dominant-balance budget separated from size. -/
structure DominantBalanceRefinementCertificate where
  dominantWindow : ℕ
  lowerWindow : ℕ
  errorWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DominantBalanceRefinementCertificate.balanceControlled
    (cert : DominantBalanceRefinementCertificate) : Prop :=
  0 < cert.dominantWindow ∧
    cert.lowerWindow + cert.errorWindow ≤ cert.dominantWindow + cert.slack

def DominantBalanceRefinementCertificate.budgetControlled
    (cert : DominantBalanceRefinementCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.dominantWindow + cert.lowerWindow + cert.errorWindow + cert.slack

def dominantBalanceRefinementReady
    (cert : DominantBalanceRefinementCertificate) : Prop :=
  cert.balanceControlled ∧ cert.budgetControlled

def DominantBalanceRefinementCertificate.size
    (cert : DominantBalanceRefinementCertificate) : ℕ :=
  cert.dominantWindow + cert.lowerWindow + cert.errorWindow + cert.slack

theorem dominantBalance_certificateBudgetWindow_le_size
    (cert : DominantBalanceRefinementCertificate)
    (h : dominantBalanceRefinementReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleDominantBalanceRefinementCertificate :
    DominantBalanceRefinementCertificate :=
  { dominantWindow := 14, lowerWindow := 5, errorWindow := 3,
    certificateBudgetWindow := 23, slack := 1 }

example :
    dominantBalanceRefinementReady sampleDominantBalanceRefinementCertificate := by
  norm_num [dominantBalanceRefinementReady,
    DominantBalanceRefinementCertificate.balanceControlled,
    DominantBalanceRefinementCertificate.budgetControlled,
    sampleDominantBalanceRefinementCertificate]

example :
    sampleDominantBalanceRefinementCertificate.certificateBudgetWindow ≤
      sampleDominantBalanceRefinementCertificate.size := by
  apply dominantBalance_certificateBudgetWindow_le_size
  norm_num [dominantBalanceRefinementReady,
    DominantBalanceRefinementCertificate.balanceControlled,
    DominantBalanceRefinementCertificate.budgetControlled,
    sampleDominantBalanceRefinementCertificate]


structure DominantBalanceSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DominantBalanceSchemasBudgetCertificate.controlled
    (c : DominantBalanceSchemasBudgetCertificate) : Prop :=
  0 < c.primaryWindow ∧ c.secondaryWindow ≤ c.primaryWindow + c.slack

def DominantBalanceSchemasBudgetCertificate.budgetControlled
    (c : DominantBalanceSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def DominantBalanceSchemasBudgetCertificate.Ready
    (c : DominantBalanceSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def DominantBalanceSchemasBudgetCertificate.size
    (c : DominantBalanceSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem dominantBalanceSchemas_budgetCertificate_le_size
    (c : DominantBalanceSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleDominantBalanceSchemasBudgetCertificate :
    DominantBalanceSchemasBudgetCertificate :=
  { primaryWindow := 5
    secondaryWindow := 6
    certificateBudgetWindow := 12
    slack := 1 }

example : sampleDominantBalanceSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [DominantBalanceSchemasBudgetCertificate.controlled,
      sampleDominantBalanceSchemasBudgetCertificate]
  · norm_num [DominantBalanceSchemasBudgetCertificate.budgetControlled,
      sampleDominantBalanceSchemasBudgetCertificate]

example :
    sampleDominantBalanceSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleDominantBalanceSchemasBudgetCertificate.size := by
  apply dominantBalanceSchemas_budgetCertificate_le_size
  constructor
  · norm_num [DominantBalanceSchemasBudgetCertificate.controlled,
      sampleDominantBalanceSchemasBudgetCertificate]
  · norm_num [DominantBalanceSchemasBudgetCertificate.budgetControlled,
      sampleDominantBalanceSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleDominantBalanceSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [DominantBalanceSchemasBudgetCertificate.controlled,
      sampleDominantBalanceSchemasBudgetCertificate]
  · norm_num [DominantBalanceSchemasBudgetCertificate.budgetControlled,
      sampleDominantBalanceSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleDominantBalanceSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleDominantBalanceSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List DominantBalanceSchemasBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleDominantBalanceSchemasBudgetCertificate] =
      true := by
  unfold budgetCertificateListReady sampleDominantBalanceSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.Asymptotics.DominantBalanceSchemas
