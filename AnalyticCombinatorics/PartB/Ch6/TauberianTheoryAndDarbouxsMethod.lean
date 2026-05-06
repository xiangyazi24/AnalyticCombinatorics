import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Tauberian theory and Darboux's method
-/

namespace AnalyticCombinatorics.PartB.Ch6.TauberianTheoryAndDarbouxsMethod

/-- Partial sums used in one-sided Tauberian transfer. -/
def partialSum (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  (List.range (n + 1)).foldl (fun total k => total + a k) 0

theorem partialSum_zero (a : ℕ → ℕ) :
    partialSum a 0 = a 0 := by
  simp [partialSum]

theorem partialSum_const_one_samples :
    partialSum (fun _ => 1) 0 = 1 ∧
      partialSum (fun _ => 1) 4 = 5 := by
  native_decide

/-- Darboux local coefficient truncation at a finite order. -/
def darbouxTruncation (coeff : ℕ → ℤ) (order n : ℕ) : ℤ :=
  if n < order then coeff n else 0

theorem darbouxTruncation_of_lt
    {coeff : ℕ → ℤ} {order n : ℕ} (h : n < order) :
    darbouxTruncation coeff order n = coeff n := by
  simp [darbouxTruncation, h]

theorem darbouxTruncation_of_not_lt
    {coeff : ℕ → ℤ} {order n : ℕ} (h : ¬ n < order) :
    darbouxTruncation coeff order n = 0 := by
  simp [darbouxTruncation, h]

/-- Finite Abelian side audit: coefficients are bounded by partial sums. -/
def coefficientBelowPartialSum (a : ℕ → ℕ) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => a n ≤ partialSum a n

theorem coefficientBelowPartialSum_const_one :
    coefficientBelowPartialSum (fun _ => 1) 8 = true := by
  unfold coefficientBelowPartialSum partialSum
  native_decide

structure DarbouxTauberianWindow where
  tauberianWindow : ℕ
  darbouxWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DarbouxTauberianWindow.controlled
    (w : DarbouxTauberianWindow) : Prop :=
  0 < w.tauberianWindow ∧
    w.darbouxWindow ≤ w.tauberianWindow + w.slack

def DarbouxTauberianWindow.budgetControlled
    (w : DarbouxTauberianWindow) : Prop :=
  w.certificateBudgetWindow ≤
    w.tauberianWindow + w.darbouxWindow + w.slack

def DarbouxTauberianWindow.Ready (w : DarbouxTauberianWindow) : Prop :=
  w.controlled ∧ w.budgetControlled

def DarbouxTauberianWindow.size (w : DarbouxTauberianWindow) : ℕ :=
  w.tauberianWindow + w.darbouxWindow + w.slack

def sampleDarbouxTauberianWindow : DarbouxTauberianWindow :=
  { tauberianWindow := 2
    darbouxWindow := 3
    certificateBudgetWindow := 6
    slack := 1 }

example : sampleDarbouxTauberianWindow.Ready := by
  constructor <;> norm_num
    [DarbouxTauberianWindow.controlled,
      DarbouxTauberianWindow.budgetControlled, sampleDarbouxTauberianWindow]

abbrev BudgetCertificate := DarbouxTauberianWindow

def sampleBudgetCertificate : BudgetCertificate :=
  sampleDarbouxTauberianWindow

theorem sampleBudgetCertificate_ready :
    sampleBudgetCertificate.Ready := by
  constructor <;> norm_num
    [DarbouxTauberianWindow.controlled,
      DarbouxTauberianWindow.budgetControlled, sampleBudgetCertificate,
      sampleDarbouxTauberianWindow]

theorem sampleBudgetCertificate_le_size :
    sampleBudgetCertificate.certificateBudgetWindow ≤
      sampleBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List DarbouxTauberianWindow) : Bool :=
  data.all fun w => w.certificateBudgetWindow ≤ w.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleDarbouxTauberianWindow] = true := by
  unfold budgetCertificateListReady sampleDarbouxTauberianWindow
  native_decide

example :
    budgetCertificateListReady
      [sampleDarbouxTauberianWindow] = true := by
  exact budgetCertificateList_readyWindow

end AnalyticCombinatorics.PartB.Ch6.TauberianTheoryAndDarbouxsMethod
