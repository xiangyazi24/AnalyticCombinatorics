import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Saddle-point examples.

This module records finite bookkeeping for saddle-point coefficient windows.
-/

namespace AnalyticCombinatorics.PartB.Ch8.SaddlePoint

structure SaddleWindow where
  saddleScale : ℕ
  gaussianWidth : ℕ
  errorSlack : ℕ
deriving DecidableEq, Repr

def saddleReady (w : SaddleWindow) : Prop :=
  0 < w.saddleScale ∧ w.gaussianWidth ≤ w.saddleScale + w.errorSlack

def saddleBudget (w : SaddleWindow) : ℕ :=
  w.saddleScale + w.gaussianWidth + w.errorSlack

theorem saddleReady.scale_pos {w : SaddleWindow} (h : saddleReady w) :
    0 < w.saddleScale := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem gaussianWidth_le_budget (w : SaddleWindow) :
    w.gaussianWidth ≤ saddleBudget w := by
  unfold saddleBudget
  omega

def sampleSaddleWindow : SaddleWindow :=
  { saddleScale := 8, gaussianWidth := 10, errorSlack := 3 }

example : saddleReady sampleSaddleWindow := by
  norm_num [saddleReady, sampleSaddleWindow]

example : saddleBudget sampleSaddleWindow = 21 := by
  native_decide

structure SaddleCoefficientWindow where
  saddleIndex : ℕ
  localMass : ℕ
  gaussianMass : ℕ
  tailMass : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SaddleCoefficientWindow.totalMass (w : SaddleCoefficientWindow) : ℕ :=
  w.localMass + w.gaussianMass + w.tailMass

def SaddleCoefficientWindow.tailControlled (w : SaddleCoefficientWindow) : Prop :=
  w.tailMass ≤ w.gaussianMass + w.slack

def SaddleCoefficientWindow.ready (w : SaddleCoefficientWindow) : Prop :=
  0 < w.saddleIndex ∧ w.tailControlled

def SaddleCoefficientWindow.certificate (w : SaddleCoefficientWindow) : ℕ :=
  w.saddleIndex + w.localMass + w.gaussianMass + w.tailMass + w.slack

theorem tailMass_le_certificate (w : SaddleCoefficientWindow) :
    w.tailMass ≤ w.certificate := by
  unfold SaddleCoefficientWindow.certificate
  omega

def sampleSaddleCoefficientWindow : SaddleCoefficientWindow :=
  { saddleIndex := 5, localMass := 20, gaussianMass := 12, tailMass := 4, slack := 0 }

example : sampleSaddleCoefficientWindow.ready := by
  norm_num [sampleSaddleCoefficientWindow, SaddleCoefficientWindow.ready,
    SaddleCoefficientWindow.tailControlled]

example : sampleSaddleCoefficientWindow.totalMass = 36 := by
  native_decide


structure SaddlePointBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SaddlePointBudgetCertificate.controlled
    (c : SaddlePointBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def SaddlePointBudgetCertificate.budgetControlled
    (c : SaddlePointBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def SaddlePointBudgetCertificate.Ready
    (c : SaddlePointBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SaddlePointBudgetCertificate.size
    (c : SaddlePointBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem saddlePoint_budgetCertificate_le_size
    (c : SaddlePointBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSaddlePointBudgetCertificate :
    SaddlePointBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleSaddlePointBudgetCertificate.Ready := by
  constructor
  · norm_num [SaddlePointBudgetCertificate.controlled,
      sampleSaddlePointBudgetCertificate]
  · norm_num [SaddlePointBudgetCertificate.budgetControlled,
      sampleSaddlePointBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSaddlePointBudgetCertificate.certificateBudgetWindow ≤
      sampleSaddlePointBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleSaddlePointBudgetCertificate.Ready := by
  constructor
  · norm_num [SaddlePointBudgetCertificate.controlled,
      sampleSaddlePointBudgetCertificate]
  · norm_num [SaddlePointBudgetCertificate.budgetControlled,
      sampleSaddlePointBudgetCertificate]

example :
    sampleSaddlePointBudgetCertificate.certificateBudgetWindow ≤
      sampleSaddlePointBudgetCertificate.size := by
  apply saddlePoint_budgetCertificate_le_size
  constructor
  · norm_num [SaddlePointBudgetCertificate.controlled,
      sampleSaddlePointBudgetCertificate]
  · norm_num [SaddlePointBudgetCertificate.budgetControlled,
      sampleSaddlePointBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List SaddlePointBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSaddlePointBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleSaddlePointBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch8.SaddlePoint
