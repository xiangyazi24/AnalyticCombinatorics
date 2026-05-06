import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Abelian partial-sum schema bookkeeping.

The file records finite partial sums and Abelian error budgets.
-/

namespace AnalyticCombinatorics.AppC.AbelianPartialSumSchemas

def partialSum (a : ℕ → ℕ) (N : ℕ) : ℕ :=
  (List.range (N + 1)).map a |>.sum

def partialSumBounded (a : ℕ → ℕ) (N bound : ℕ) : Prop :=
  partialSum a N ≤ bound

def constantSeq (c : ℕ) (n : ℕ) : ℕ := c + (n - n)

theorem partialSum_zero (a : ℕ → ℕ) :
    partialSum a 0 = a 0 := by
  simp [partialSum]

theorem partialSumBounded_mono {a : ℕ → ℕ} {N b c : ℕ}
    (h : partialSumBounded a N b) (hbc : b ≤ c) :
    partialSumBounded a N c := by
  unfold partialSumBounded at *
  omega

example : partialSum (constantSeq 4) 3 = 16 := by
  native_decide

example : partialSum (constantSeq 4) 3 ≤ 20 := by
  native_decide

structure AbelianPartialSumWindow where
  cutoff : ℕ
  partialMass : ℕ
  tailAllowance : ℕ
  targetBound : ℕ
deriving DecidableEq, Repr

def AbelianPartialSumWindow.totalAllowance (w : AbelianPartialSumWindow) : ℕ :=
  w.partialMass + w.tailAllowance

def AbelianPartialSumWindow.ready (w : AbelianPartialSumWindow) : Prop :=
  w.totalAllowance ≤ w.targetBound

def AbelianPartialSumWindow.nontrivialCutoff (w : AbelianPartialSumWindow) : Prop :=
  0 < w.cutoff

def AbelianPartialSumWindow.certificate (w : AbelianPartialSumWindow) : ℕ :=
  w.cutoff + w.partialMass + w.tailAllowance + w.targetBound

theorem partialMass_le_certificate (w : AbelianPartialSumWindow) :
    w.partialMass ≤ w.certificate := by
  unfold AbelianPartialSumWindow.certificate
  omega

theorem tailAllowance_le_certificate (w : AbelianPartialSumWindow) :
    w.tailAllowance ≤ w.certificate := by
  unfold AbelianPartialSumWindow.certificate
  omega

def sampleAbelianPartialSumWindow : AbelianPartialSumWindow :=
  { cutoff := 4, partialMass := 16, tailAllowance := 3, targetBound := 20 }

example : sampleAbelianPartialSumWindow.ready := by
  norm_num [sampleAbelianPartialSumWindow, AbelianPartialSumWindow.ready,
    AbelianPartialSumWindow.totalAllowance]

example : sampleAbelianPartialSumWindow.nontrivialCutoff := by
  norm_num [sampleAbelianPartialSumWindow, AbelianPartialSumWindow.nontrivialCutoff]

structure AbelianPartialSumRefinementWindow where
  cutoffWindow : ℕ
  partialWindow : ℕ
  tailWindow : ℕ
  abelianBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AbelianPartialSumRefinementWindow.tailControlled
    (w : AbelianPartialSumRefinementWindow) : Prop :=
  w.tailWindow ≤ w.partialWindow + w.slack

def abelianPartialSumRefinementReady
    (w : AbelianPartialSumRefinementWindow) : Prop :=
  0 < w.cutoffWindow ∧ w.tailControlled ∧
    w.abelianBudget ≤ w.cutoffWindow + w.partialWindow + w.tailWindow + w.slack

def AbelianPartialSumRefinementWindow.certificate
    (w : AbelianPartialSumRefinementWindow) : ℕ :=
  w.cutoffWindow + w.partialWindow + w.tailWindow + w.abelianBudget + w.slack

theorem abelianPartialSum_budget_le_certificate
    (w : AbelianPartialSumRefinementWindow) :
    w.abelianBudget ≤ w.certificate := by
  unfold AbelianPartialSumRefinementWindow.certificate
  omega

def sampleAbelianPartialSumRefinementWindow :
    AbelianPartialSumRefinementWindow :=
  { cutoffWindow := 4, partialWindow := 16, tailWindow := 3,
    abelianBudget := 24, slack := 1 }

example : abelianPartialSumRefinementReady
    sampleAbelianPartialSumRefinementWindow := by
  norm_num [abelianPartialSumRefinementReady,
    AbelianPartialSumRefinementWindow.tailControlled, sampleAbelianPartialSumRefinementWindow]


structure AbelianPartialSumSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AbelianPartialSumSchemasBudgetCertificate.controlled
    (c : AbelianPartialSumSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AbelianPartialSumSchemasBudgetCertificate.budgetControlled
    (c : AbelianPartialSumSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AbelianPartialSumSchemasBudgetCertificate.Ready
    (c : AbelianPartialSumSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AbelianPartialSumSchemasBudgetCertificate.size
    (c : AbelianPartialSumSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem abelianPartialSumSchemas_budgetCertificate_le_size
    (c : AbelianPartialSumSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAbelianPartialSumSchemasBudgetCertificate :
    AbelianPartialSumSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleAbelianPartialSumSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [AbelianPartialSumSchemasBudgetCertificate.controlled,
      sampleAbelianPartialSumSchemasBudgetCertificate]
  · norm_num [AbelianPartialSumSchemasBudgetCertificate.budgetControlled,
      sampleAbelianPartialSumSchemasBudgetCertificate]

example :
    sampleAbelianPartialSumSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleAbelianPartialSumSchemasBudgetCertificate.size := by
  apply abelianPartialSumSchemas_budgetCertificate_le_size
  constructor
  · norm_num [AbelianPartialSumSchemasBudgetCertificate.controlled,
      sampleAbelianPartialSumSchemasBudgetCertificate]
  · norm_num [AbelianPartialSumSchemasBudgetCertificate.budgetControlled,
      sampleAbelianPartialSumSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleAbelianPartialSumSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [AbelianPartialSumSchemasBudgetCertificate.controlled,
      sampleAbelianPartialSumSchemasBudgetCertificate]
  · norm_num [AbelianPartialSumSchemasBudgetCertificate.budgetControlled,
      sampleAbelianPartialSumSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAbelianPartialSumSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleAbelianPartialSumSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List AbelianPartialSumSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAbelianPartialSumSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAbelianPartialSumSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.AbelianPartialSumSchemas
