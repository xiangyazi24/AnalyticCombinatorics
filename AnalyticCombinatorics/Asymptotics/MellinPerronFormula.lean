import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Mellin-Perron formula
-/

namespace AnalyticCombinatorics.Asymptotics.MellinPerronFormula

/-- Finite Dirichlet prefix used in Mellin-Perron summation. -/
def dirichletPrefix (a : ℕ → ℕ) (N : ℕ) : ℕ :=
  (List.range (N + 1)).foldl (fun total n => total + a n) 0

theorem dirichletPrefix_zero (a : ℕ → ℕ) :
    dirichletPrefix a 0 = a 0 := by
  simp [dirichletPrefix]

def harmonicNumeratorPrefix (N : ℕ) : ℕ :=
  dirichletPrefix (fun n => n + 1) N

theorem harmonicNumeratorPrefix_samples :
    harmonicNumeratorPrefix 0 = 1 ∧
      harmonicNumeratorPrefix 3 = 10 := by
  native_decide

/-- Perron cutoff kernel for finite summatory functions. -/
def perronCutoff (cutoff n : ℕ) : ℕ :=
  if n ≤ cutoff then 1 else 0

theorem perronCutoff_of_le {cutoff n : ℕ} (h : n ≤ cutoff) :
    perronCutoff cutoff n = 1 := by
  simp [perronCutoff, h]

def mellinPerronSummatory (a : ℕ → ℕ) (cutoff N : ℕ) : ℕ :=
  (List.range (N + 1)).foldl
    (fun total n => total + perronCutoff cutoff n * a n) 0

theorem mellinPerronSummatory_const_one :
    mellinPerronSummatory (fun _ => 1) 3 6 = 4 := by
  unfold mellinPerronSummatory perronCutoff
  native_decide

structure MellinPerronWindow where
  mellinWindow : ℕ
  perronWindow : ℕ
  inversionWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MellinPerronWindow.ready (w : MellinPerronWindow) : Prop :=
  0 < w.mellinWindow ∧
    w.inversionWindow ≤ w.mellinWindow + w.perronWindow + w.slack

def sampleMellinPerronWindow : MellinPerronWindow :=
  { mellinWindow := 4, perronWindow := 3,
    inversionWindow := 7, slack := 0 }

example : sampleMellinPerronWindow.ready := by
  norm_num [MellinPerronWindow.ready, sampleMellinPerronWindow]

structure BudgetCertificate where
  mellinWindow : ℕ
  perronWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.mellinWindow ∧ c.perronWindow ≤ c.mellinWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.mellinWindow + c.perronWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.mellinWindow + c.perronWindow + c.slack

theorem mellinPerronFormula_budgetCertificate_le_size
    (c : BudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleBudgetCertificate : BudgetCertificate :=
  { mellinWindow := 5, perronWindow := 6, certificateBudgetWindow := 12,
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

end AnalyticCombinatorics.Asymptotics.MellinPerronFormula
