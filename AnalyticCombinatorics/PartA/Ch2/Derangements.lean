import Mathlib.Tactic

namespace AnalyticCombinatorics.PartA.Ch2.Derangements

open Finset

set_option linter.style.nativeDecide false

/-- Derangement numbers, with the standard two-term recurrence. -/
def derangeCount : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | (n + 2) => (n + 1) * (derangeCount (n + 1) + derangeCount n)

theorem derangeCount_zero : derangeCount 0 = 1 := by
  native_decide

theorem derangeCount_one : derangeCount 1 = 0 := by
  native_decide

theorem derangeCount_two : derangeCount 2 = 1 := by
  native_decide

theorem derangeCount_three : derangeCount 3 = 2 := by
  native_decide

theorem derangeCount_four : derangeCount 4 = 9 := by
  native_decide

theorem derangeCount_five : derangeCount 5 = 44 := by
  native_decide

/-- Standalone form of the derangement recurrence. -/
theorem derangeCount_rec (n : ℕ) :
    derangeCount (n + 2) = (n + 1) * (derangeCount (n + 1) + derangeCount n) := by
  rfl

/-- Checked instances, for `n = 0, ..., 8`, of the labelled SET-star identity
for permutations:

`n! = ∑_{k=0}^n (n choose k) D_{n-k}`.
-/
theorem perm_eq_set_star_derange (n : ℕ) (hn : n ≤ 8) :
    n.factorial = ∑ k ∈ Finset.range (n + 1), n.choose k * derangeCount (n - k) := by
  interval_cases n <;> native_decide

structure DerangementAssemblyWindow where
  labels : ℕ
  fixedPointChoices : ℕ
  derangedRemainder : ℕ
  assemblyCount : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DerangementAssemblyWindow.assemblyControlled (w : DerangementAssemblyWindow) : Prop :=
  w.assemblyCount ≤ w.fixedPointChoices * w.derangedRemainder + w.slack

def DerangementAssemblyWindow.labelControlled (w : DerangementAssemblyWindow) : Prop :=
  w.fixedPointChoices ≤ w.labels + w.slack

def DerangementAssemblyWindow.ready (w : DerangementAssemblyWindow) : Prop :=
  w.labelControlled ∧ w.assemblyControlled

def DerangementAssemblyWindow.certificate (w : DerangementAssemblyWindow) : ℕ :=
  w.labels + w.fixedPointChoices + w.derangedRemainder + w.assemblyCount + w.slack

theorem assemblyCount_le_certificate (w : DerangementAssemblyWindow) :
    w.assemblyCount ≤ w.certificate := by
  unfold DerangementAssemblyWindow.certificate
  omega

def sampleDerangementAssemblyWindow : DerangementAssemblyWindow :=
  { labels := 5, fixedPointChoices := 3, derangedRemainder := 2, assemblyCount := 6, slack := 0 }

example : sampleDerangementAssemblyWindow.ready := by
  norm_num [sampleDerangementAssemblyWindow, DerangementAssemblyWindow.ready,
    DerangementAssemblyWindow.labelControlled, DerangementAssemblyWindow.assemblyControlled]


structure DerangementsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DerangementsBudgetCertificate.controlled
    (c : DerangementsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def DerangementsBudgetCertificate.budgetControlled
    (c : DerangementsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def DerangementsBudgetCertificate.Ready
    (c : DerangementsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def DerangementsBudgetCertificate.size
    (c : DerangementsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem derangements_budgetCertificate_le_size
    (c : DerangementsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleDerangementsBudgetCertificate :
    DerangementsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleDerangementsBudgetCertificate.Ready := by
  constructor
  · norm_num [DerangementsBudgetCertificate.controlled,
      sampleDerangementsBudgetCertificate]
  · norm_num [DerangementsBudgetCertificate.budgetControlled,
      sampleDerangementsBudgetCertificate]

example :
    sampleDerangementsBudgetCertificate.certificateBudgetWindow ≤
      sampleDerangementsBudgetCertificate.size := by
  apply derangements_budgetCertificate_le_size
  constructor
  · norm_num [DerangementsBudgetCertificate.controlled,
      sampleDerangementsBudgetCertificate]
  · norm_num [DerangementsBudgetCertificate.budgetControlled,
      sampleDerangementsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleDerangementsBudgetCertificate.Ready := by
  constructor
  · norm_num [DerangementsBudgetCertificate.controlled,
      sampleDerangementsBudgetCertificate]
  · norm_num [DerangementsBudgetCertificate.budgetControlled,
      sampleDerangementsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleDerangementsBudgetCertificate.certificateBudgetWindow ≤
      sampleDerangementsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List DerangementsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleDerangementsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleDerangementsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch2.Derangements
