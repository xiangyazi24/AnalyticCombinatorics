import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Perron formula
-/

namespace AnalyticCombinatorics.Asymptotics.PerronFormula

/-- Finite Perron step kernel: terms up to the cutoff are retained. -/
def perronStepIndicator (cutoff n : ℕ) : ℕ :=
  if n ≤ cutoff then 1 else 0

theorem perronStepIndicator_of_le {cutoff n : ℕ} (h : n ≤ cutoff) :
    perronStepIndicator cutoff n = 1 := by
  simp [perronStepIndicator, h]

theorem perronStepIndicator_of_not_le {cutoff n : ℕ} (h : ¬ n ≤ cutoff) :
    perronStepIndicator cutoff n = 0 := by
  simp [perronStepIndicator, h]

/-- Finite Perron counting sum for a Dirichlet-coefficient prefix. -/
def perronCountingSum (a : ℕ → ℕ) (cutoff N : ℕ) : ℕ :=
  (List.range (N + 1)).foldl
    (fun s n => s + perronStepIndicator cutoff n * a n) 0

theorem perronCountingSum_zero_bound (a : ℕ → ℕ) :
    perronCountingSum a 0 0 = a 0 := by
  simp [perronCountingSum, perronStepIndicator]

theorem perronCountingSum_const_one_samples :
    perronCountingSum (fun _ => 1) 0 4 = 1 ∧
      perronCountingSum (fun _ => 1) 2 4 = 3 ∧
        perronCountingSum (fun _ => 1) 4 4 = 5 := by
  native_decide

/-- Monotonicity audit in the Perron cutoff parameter. -/
def perronCutoffMonotoneUpTo (a : ℕ → ℕ) (N : ℕ) : Bool :=
  (List.range N).all fun cutoff =>
    perronCountingSum a cutoff N ≤ perronCountingSum a (cutoff + 1) N

theorem perronCutoffMonotone_const_one_12 :
    perronCutoffMonotoneUpTo (fun _ => 1) 12 = true := by
  unfold perronCutoffMonotoneUpTo perronCountingSum perronStepIndicator
  native_decide

structure PerronWindow where
  verticalLineWindow : ℕ
  residueWindow : ℕ
  truncationWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PerronWindow.ready (w : PerronWindow) : Prop :=
  0 < w.verticalLineWindow ∧
    w.truncationWindow ≤ w.verticalLineWindow + w.residueWindow + w.slack

def samplePerronWindow : PerronWindow :=
  { verticalLineWindow := 4, residueWindow := 3,
    truncationWindow := 7, slack := 0 }

example : samplePerronWindow.ready := by
  norm_num [PerronWindow.ready, samplePerronWindow]

structure BudgetCertificate where
  lineWindow : ℕ
  residueWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.lineWindow ∧ c.residueWindow ≤ c.lineWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.lineWindow + c.residueWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.lineWindow + c.residueWindow + c.slack

def sampleBudgetCertificate : BudgetCertificate :=
  { lineWindow := 5, residueWindow := 6, certificateBudgetWindow := 12,
    slack := 1 }

example : sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled, sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled, sampleBudgetCertificate]

theorem sampleBudgetCertificate_ready :
    sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled,
      sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled,
      sampleBudgetCertificate]

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

end AnalyticCombinatorics.Asymptotics.PerronFormula
