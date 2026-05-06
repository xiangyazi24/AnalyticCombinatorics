import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Tauberian theorems
-/

namespace AnalyticCombinatorics.Asymptotics.TauberianTheorems

/-- Partial sums for nonnegative coefficient sequences. -/
def partialSum (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  (List.range (n + 1)).foldl (fun s k => s + a k) 0

theorem partialSum_zero (a : ℕ → ℕ) :
    partialSum a 0 = a 0 := by
  simp [partialSum]

theorem partialSum_const_one (n : ℕ) :
    partialSum (fun _ => 1) n = n + 1 := by
  induction n with
  | zero =>
      simp [partialSum]
  | succ n ih =>
      unfold partialSum at ih ⊢
      rw [List.range_succ]
      simp [List.foldl_append, ih]

/-- Boolean monotonicity audit for Tauberian nondecreasing partial sums. -/
def partialSumsMonotoneUpTo (a : ℕ → ℕ) (N : ℕ) : Bool :=
  (List.range N).all fun n => partialSum a n ≤ partialSum a (n + 1)

theorem partialSumsMonotone_const_one (N : ℕ) :
    partialSumsMonotoneUpTo (fun _ => 1) N = true := by
  unfold partialSumsMonotoneUpTo
  simp [partialSum_const_one]

structure TauberianWindow where
  abelianWindow : ℕ
  tauberianWindow : ℕ
  remainderWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TauberianWindow.ready (w : TauberianWindow) : Prop :=
  0 < w.tauberianWindow ∧
    w.remainderWindow ≤ w.abelianWindow + w.tauberianWindow + w.slack

def sampleTauberianWindow : TauberianWindow :=
  { abelianWindow := 4, tauberianWindow := 3,
    remainderWindow := 7, slack := 0 }

example : sampleTauberianWindow.ready := by
  norm_num [TauberianWindow.ready, sampleTauberianWindow]

structure BudgetCertificate where
  tauberianWindow : ℕ
  remainderWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.tauberianWindow ∧
    c.remainderWindow ≤ c.tauberianWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.tauberianWindow + c.remainderWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.tauberianWindow + c.remainderWindow + c.slack

theorem tauberianTheorems_budgetCertificate_le_size
    (c : BudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleBudgetCertificate : BudgetCertificate :=
  { tauberianWindow := 5, remainderWindow := 6,
    certificateBudgetWindow := 12, slack := 1 }

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

end AnalyticCombinatorics.Asymptotics.TauberianTheorems
