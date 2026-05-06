import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Appendix A: asymptotic notations.

Finite dominance windows for O, o, Theta, and equivalent-scale bookkeeping.
-/

namespace AnalyticCombinatorics.AppA.AsymptoticNotations

/-- Finite big-O check: `a n <= C * b n` after a threshold. -/
def bigOCheck (a b : ℕ → ℕ) (C threshold N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    if n < threshold then true else a n ≤ C * b n

/-- Finite little-o certificate: ratio is below a fixed inverse tolerance. -/
def littleOCheck (a b : ℕ → ℕ) (denom threshold N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    if n < threshold then true else denom * a n ≤ b n

/-- Finite theta check with lower and upper integer constants. -/
def thetaCheck (a b : ℕ → ℕ) (lower upper threshold N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    if n < threshold then true else lower * b n ≤ a n ∧ a n ≤ upper * b n

theorem linear_bigO_quadratic :
    bigOCheck (fun n => n) (fun n => n ^ 2) 1 1 24 = true := by
  unfold bigOCheck
  native_decide

theorem linear_littleO_quadratic_window :
    littleOCheck (fun n => n) (fun n => n ^ 2) 10 10 40 = true := by
  unfold littleOCheck
  native_decide

theorem quadratic_theta_self :
    thetaCheck (fun n => n ^ 2) (fun n => n ^ 2) 1 1 0 24 = true := by
  unfold thetaCheck
  native_decide

structure DominanceWindow where
  baseScale : ℕ
  comparisonScale : ℕ
  threshold : ℕ
  notationSlack : ℕ
deriving DecidableEq, Repr

def dominanceWindowReady (w : DominanceWindow) : Prop :=
  0 < w.baseScale ∧
    w.comparisonScale ≤ w.baseScale * (w.threshold + 1) + w.notationSlack

def dominanceWindowBudget (w : DominanceWindow) : ℕ :=
  w.baseScale + w.comparisonScale + w.threshold + w.notationSlack

theorem comparisonScale_le_budget (w : DominanceWindow) :
    w.comparisonScale ≤ dominanceWindowBudget w + w.baseScale * w.threshold := by
  unfold dominanceWindowBudget
  omega

def sampleDominanceWindow : DominanceWindow :=
  { baseScale := 3, comparisonScale := 10, threshold := 3, notationSlack := 1 }

example : dominanceWindowReady sampleDominanceWindow := by
  norm_num [dominanceWindowReady, sampleDominanceWindow]

structure AsymptoticNotationsBudgetCertificate where
  baseWindow : ℕ
  comparisonWindow : ℕ
  thresholdWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AsymptoticNotationsBudgetCertificate.controlled
    (c : AsymptoticNotationsBudgetCertificate) : Prop :=
  0 < c.baseWindow ∧
    c.comparisonWindow ≤ c.baseWindow * (c.thresholdWindow + 1) + c.slack

def AsymptoticNotationsBudgetCertificate.budgetControlled
    (c : AsymptoticNotationsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.baseWindow + c.comparisonWindow + c.thresholdWindow + c.slack

def AsymptoticNotationsBudgetCertificate.Ready
    (c : AsymptoticNotationsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AsymptoticNotationsBudgetCertificate.size
    (c : AsymptoticNotationsBudgetCertificate) : ℕ :=
  c.baseWindow + c.comparisonWindow + c.thresholdWindow + c.slack

theorem asymptoticNotations_budgetCertificate_le_size
    (c : AsymptoticNotationsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleAsymptoticNotationsBudgetCertificate :
    AsymptoticNotationsBudgetCertificate :=
  { baseWindow := 3
    comparisonWindow := 10
    thresholdWindow := 3
    certificateBudgetWindow := 17
    slack := 1 }

example : sampleAsymptoticNotationsBudgetCertificate.Ready := by
  constructor
  · norm_num [AsymptoticNotationsBudgetCertificate.controlled,
      sampleAsymptoticNotationsBudgetCertificate]
  · norm_num [AsymptoticNotationsBudgetCertificate.budgetControlled,
      sampleAsymptoticNotationsBudgetCertificate]

/-- Finite executable readiness audit for asymptotic-notation certificates. -/
def asymptoticNotationsBudgetCertificateListReady
    (data : List AsymptoticNotationsBudgetCertificate) : Bool :=
  data.all fun c =>
    0 < c.baseWindow &&
      c.comparisonWindow ≤ c.baseWindow * (c.thresholdWindow + 1) + c.slack &&
        c.certificateBudgetWindow ≤
          c.baseWindow + c.comparisonWindow + c.thresholdWindow + c.slack

theorem asymptoticNotationsBudgetCertificateList_readyWindow :
    asymptoticNotationsBudgetCertificateListReady
      [sampleAsymptoticNotationsBudgetCertificate,
       { baseWindow := 2, comparisonWindow := 7, thresholdWindow := 3,
         certificateBudgetWindow := 13, slack := 1 }] = true := by
  unfold asymptoticNotationsBudgetCertificateListReady
    sampleAsymptoticNotationsBudgetCertificate
  native_decide

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleAsymptoticNotationsBudgetCertificate.Ready := by
  constructor
  · norm_num [AsymptoticNotationsBudgetCertificate.controlled,
      sampleAsymptoticNotationsBudgetCertificate]
  · norm_num [AsymptoticNotationsBudgetCertificate.budgetControlled,
      sampleAsymptoticNotationsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAsymptoticNotationsBudgetCertificate.certificateBudgetWindow ≤
      sampleAsymptoticNotationsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List AsymptoticNotationsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAsymptoticNotationsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleAsymptoticNotationsBudgetCertificate
  native_decide
end AnalyticCombinatorics.AppA.AsymptoticNotations
