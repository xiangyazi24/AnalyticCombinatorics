import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Local limit theorems
-/

namespace AnalyticCombinatorics.Asymptotics.LocalLimitTheorems

/-- Lattice span compatibility for a sampled local limit window. -/
def latticeCompatible (span location : ℕ) : Bool :=
  if span = 0 then false else span ∣ location

theorem latticeCompatible_self {span : ℕ} (h : span ≠ 0) :
    latticeCompatible span span = true := by
  simp [latticeCompatible, h]

/-- Local mass envelope on a lattice point. -/
def localMassEnvelope (varianceWindow heightWindow : ℕ) : ℕ :=
  heightWindow / (varianceWindow + 1)

theorem localMassEnvelope_zero_height (varianceWindow : ℕ) :
    localMassEnvelope varianceWindow 0 = 0 := by
  simp [localMassEnvelope]

def localLimitWindowCheck (span variance height N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    if latticeCompatible span n then
      localMassEnvelope variance height ≤ height
    else true

theorem localLimitWindowCheck_sample :
    localLimitWindowCheck 2 3 12 8 = true := by
  unfold localLimitWindowCheck latticeCompatible localMassEnvelope
  native_decide

structure LocalLimitWindow where
  latticeWindow : ℕ
  varianceWindow : ℕ
  errorWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LocalLimitWindow.ready (w : LocalLimitWindow) : Prop :=
  0 < w.latticeWindow ∧
    w.errorWindow ≤ w.latticeWindow + w.varianceWindow + w.slack

def sampleLocalLimitWindow : LocalLimitWindow :=
  { latticeWindow := 4, varianceWindow := 3, errorWindow := 7, slack := 0 }

example : sampleLocalLimitWindow.ready := by
  norm_num [LocalLimitWindow.ready, sampleLocalLimitWindow]

structure BudgetCertificate where
  localWindow : ℕ
  errorWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.localWindow ∧ c.errorWindow ≤ c.localWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.localWindow + c.errorWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.localWindow + c.errorWindow + c.slack

theorem localLimitTheorems_budgetCertificate_le_size
    (c : BudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleBudgetCertificate : BudgetCertificate :=
  { localWindow := 5, errorWindow := 6, certificateBudgetWindow := 12,
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled, sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled, sampleBudgetCertificate]

example : sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled, sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled, sampleBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleBudgetCertificate.certificateBudgetWindow ≤
      sampleBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List BudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleBudgetCertificate
  native_decide

end AnalyticCombinatorics.Asymptotics.LocalLimitTheorems
