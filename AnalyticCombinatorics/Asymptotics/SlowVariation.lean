import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Slow variation
-/

namespace AnalyticCombinatorics.Asymptotics.SlowVariation

/-- Slowly varying rational sample family. -/
def slowToy (n : ℕ) : ℚ :=
  if n = 0 then 1 else 1 + 1 / (n : ℚ)

theorem slowToy_zero :
    slowToy 0 = 1 := by
  simp [slowToy]

theorem slowToy_samples :
    slowToy 1 = 2 ∧ slowToy 2 = 3 / 2 ∧ slowToy 4 = 5 / 4 := by
  native_decide

/-- Ratio band check for finite slow variation samples. -/
def slowRatioBandCheck (L : ℕ → ℚ) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    if n = 0 then true else
      1 / 2 ≤ L (2 * n) / L n ∧ L (2 * n) / L n ≤ 2

theorem slowToy_ratioBand :
    slowRatioBandCheck slowToy 16 = true := by
  unfold slowRatioBandCheck slowToy
  native_decide

def slowlyVaryingEnvelope (base n : ℕ) : ℕ :=
  base * (Nat.log2 (n + 1) + 1)

theorem slowlyVaryingEnvelope_pos {base : ℕ} (h : 0 < base) (n : ℕ) :
    0 < slowlyVaryingEnvelope base n := by
  unfold slowlyVaryingEnvelope
  exact Nat.mul_pos h (Nat.succ_pos _)

structure SlowVariationWindow where
  scaleWindow : ℕ
  comparisonWindow : ℕ
  remainderWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SlowVariationWindow.ready (w : SlowVariationWindow) : Prop :=
  0 < w.scaleWindow ∧
    w.remainderWindow ≤ w.scaleWindow + w.comparisonWindow + w.slack

def sampleSlowVariationWindow : SlowVariationWindow :=
  { scaleWindow := 4, comparisonWindow := 3,
    remainderWindow := 7, slack := 0 }

example : sampleSlowVariationWindow.ready := by
  norm_num [SlowVariationWindow.ready, sampleSlowVariationWindow]

structure BudgetCertificate where
  scaleWindow : ℕ
  comparisonWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.scaleWindow ∧ c.comparisonWindow ≤ c.scaleWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.scaleWindow + c.comparisonWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.scaleWindow + c.comparisonWindow + c.slack

theorem slowVariation_budgetCertificate_le_size
    (c : BudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleBudgetCertificate : BudgetCertificate :=
  { scaleWindow := 5, comparisonWindow := 6,
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

end AnalyticCombinatorics.Asymptotics.SlowVariation
