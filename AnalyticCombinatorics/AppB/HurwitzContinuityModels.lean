import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite zero-count stability models inspired by Hurwitz continuity.

The analytic hypotheses are represented by a perturbation flag; the
conclusion is the equality of zero counts in a protected domain.
-/

namespace AnalyticCombinatorics.AppB.HurwitzContinuityModels

structure ZeroCountComparison where
  referenceZeros : ℕ
  perturbedZeros : ℕ
  perturbationSmall : Prop

def zeroCountStable (c : ZeroCountComparison) : Prop :=
  c.perturbationSmall ∧ c.referenceZeros = c.perturbedZeros

def zeroCountDefect (c : ZeroCountComparison) : ℕ :=
  c.referenceZeros - c.perturbedZeros

theorem zeroCountStable.eq {c : ZeroCountComparison}
    (h : zeroCountStable c) :
    c.referenceZeros = c.perturbedZeros := by
  rcases h with ⟨hsmall, heq⟩
  exact heq

theorem zeroCountStable.defect_zero {c : ZeroCountComparison}
    (h : zeroCountStable c) :
    zeroCountDefect c = 0 := by
  unfold zeroCountDefect
  rw [h.eq]
  simp

def sampleComparison : ZeroCountComparison :=
  { referenceZeros := 4, perturbedZeros := 4, perturbationSmall := 4 = 4 }

example : zeroCountStable sampleComparison := by
  simp [zeroCountStable, sampleComparison]

example : zeroCountDefect sampleComparison = 0 := by
  native_decide

structure HurwitzWindow where
  referenceZeros : ℕ
  perturbedZeros : ℕ
  protectedRadius : ℕ
  perturbationBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def HurwitzWindow.zeroStable (w : HurwitzWindow) : Prop :=
  w.referenceZeros = w.perturbedZeros

def HurwitzWindow.perturbationControlled (w : HurwitzWindow) : Prop :=
  w.perturbationBudget ≤ w.protectedRadius + w.slack

def HurwitzWindow.ready (w : HurwitzWindow) : Prop :=
  w.zeroStable ∧ w.perturbationControlled

def HurwitzWindow.certificate (w : HurwitzWindow) : ℕ :=
  w.referenceZeros + w.perturbedZeros + w.protectedRadius + w.perturbationBudget + w.slack

theorem perturbedZeros_le_certificate (w : HurwitzWindow) :
    w.perturbedZeros ≤ w.certificate := by
  unfold HurwitzWindow.certificate
  omega

def sampleHurwitzWindow : HurwitzWindow :=
  { referenceZeros := 4, perturbedZeros := 4, protectedRadius := 10,
    perturbationBudget := 3, slack := 0 }

example : sampleHurwitzWindow.ready := by
  norm_num [sampleHurwitzWindow, HurwitzWindow.ready, HurwitzWindow.zeroStable,
    HurwitzWindow.perturbationControlled]


structure HurwitzContinuityModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def HurwitzContinuityModelsBudgetCertificate.controlled
    (c : HurwitzContinuityModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def HurwitzContinuityModelsBudgetCertificate.budgetControlled
    (c : HurwitzContinuityModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def HurwitzContinuityModelsBudgetCertificate.Ready
    (c : HurwitzContinuityModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def HurwitzContinuityModelsBudgetCertificate.size
    (c : HurwitzContinuityModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem hurwitzContinuityModels_budgetCertificate_le_size
    (c : HurwitzContinuityModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleHurwitzContinuityModelsBudgetCertificate :
    HurwitzContinuityModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleHurwitzContinuityModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [HurwitzContinuityModelsBudgetCertificate.controlled,
      sampleHurwitzContinuityModelsBudgetCertificate]
  · norm_num [HurwitzContinuityModelsBudgetCertificate.budgetControlled,
      sampleHurwitzContinuityModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleHurwitzContinuityModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleHurwitzContinuityModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleHurwitzContinuityModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [HurwitzContinuityModelsBudgetCertificate.controlled,
      sampleHurwitzContinuityModelsBudgetCertificate]
  · norm_num [HurwitzContinuityModelsBudgetCertificate.budgetControlled,
      sampleHurwitzContinuityModelsBudgetCertificate]

example :
    sampleHurwitzContinuityModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleHurwitzContinuityModelsBudgetCertificate.size := by
  apply hurwitzContinuityModels_budgetCertificate_le_size
  constructor
  · norm_num [HurwitzContinuityModelsBudgetCertificate.controlled,
      sampleHurwitzContinuityModelsBudgetCertificate]
  · norm_num [HurwitzContinuityModelsBudgetCertificate.budgetControlled,
      sampleHurwitzContinuityModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List HurwitzContinuityModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleHurwitzContinuityModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleHurwitzContinuityModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.HurwitzContinuityModels
