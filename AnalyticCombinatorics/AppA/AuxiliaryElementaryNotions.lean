import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Auxiliary elementary notions
-/

namespace AnalyticCombinatorics.AppA.AuxiliaryElementaryNotions

/-- Indicator of a decidable finite condition as a natural coefficient. -/
def indicatorNat (p : Bool) : ℕ :=
  if p then 1 else 0

theorem indicatorNat_true :
    indicatorNat true = 1 := rfl

theorem indicatorNat_false :
    indicatorNat false = 0 := rfl

/-- Closed interval cardinality on natural numbers. -/
def intervalCard (a b : ℕ) : ℕ :=
  if a ≤ b then b - a + 1 else 0

theorem intervalCard_self (a : ℕ) :
    intervalCard a a = 1 := by
  simp [intervalCard]

theorem intervalCard_of_not_le {a b : ℕ} (h : ¬ a ≤ b) :
    intervalCard a b = 0 := by
  simp [intervalCard, h]

/-- Prefix sum over `0, ..., n`. -/
def prefixSum (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  (List.range (n + 1)).foldl (fun total k => total + a k) 0

theorem prefixSum_zero (a : ℕ → ℕ) :
    prefixSum a 0 = a 0 := by
  simp [prefixSum]

theorem prefixSum_indicator_self :
    prefixSum (fun k => indicatorNat (k == 0)) 5 = 1 := by
  unfold prefixSum indicatorNat
  native_decide

example : intervalCard 3 7 = 5 := by
  unfold intervalCard
  native_decide

example : prefixSum (fun k => k) 4 = 10 := by
  unfold prefixSum
  native_decide

/-- Finite maximum certificate for two natural bounds. -/
def maxWindow (a b : ℕ) : ℕ :=
  max a b

theorem le_maxWindow_left (a b : ℕ) :
    a ≤ maxWindow a b := by
  simp [maxWindow]

theorem le_maxWindow_right (a b : ℕ) :
    b ≤ maxWindow a b := by
  simp [maxWindow]

structure BudgetCertificate where
  elementaryWindow : ℕ
  auxiliaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.elementaryWindow ∧ c.auxiliaryWindow ≤ c.elementaryWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.elementaryWindow + c.auxiliaryWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.elementaryWindow + c.auxiliaryWindow + c.slack

def sampleBudgetCertificate : BudgetCertificate :=
  { elementaryWindow := 5, auxiliaryWindow := 6,
    certificateBudgetWindow := 12, slack := 1 }

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

end AnalyticCombinatorics.AppA.AuxiliaryElementaryNotions
