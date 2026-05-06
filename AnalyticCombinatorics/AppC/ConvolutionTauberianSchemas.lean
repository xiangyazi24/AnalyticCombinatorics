import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Convolution Tauberian schema bookkeeping.

The file records finite convolution mass and domination checks for
nonnegative sequences.
-/

namespace AnalyticCombinatorics.AppC.ConvolutionTauberianSchemas

def convolutionAt (a b : ℕ → ℕ) (n : ℕ) : ℕ :=
  (List.range (n + 1)).map (fun k => a k * b (n - k)) |>.sum

def convolutionDominatedAt (a b c : ℕ → ℕ) (n : ℕ) : Prop :=
  convolutionAt a b n ≤ c n

def unitMass : ℕ → ℕ
  | 0 => 1
  | _ => 0

theorem convolutionAt_zero (a b : ℕ → ℕ) :
    convolutionAt a b 0 = a 0 * b 0 := by
  simp [convolutionAt]

theorem convolutionDominatedAt_intro {a b c : ℕ → ℕ} {n : ℕ}
    (h : convolutionAt a b n ≤ c n) :
    convolutionDominatedAt a b c n ∧ convolutionAt a b n ≤ c n := by
  exact ⟨h, h⟩

def sampleSeq : ℕ → ℕ
  | 0 => 2
  | 1 => 3
  | _ => 0

example : convolutionAt unitMass sampleSeq 1 = 3 := by
  native_decide

example : convolutionAt sampleSeq sampleSeq 1 = 12 := by
  native_decide

structure ConvolutionWindow where
  index : ℕ
  leftMass : ℕ
  rightMass : ℕ
  convolutionMass : ℕ
  dominationSlack : ℕ
deriving DecidableEq, Repr

def ConvolutionWindow.massBudget (w : ConvolutionWindow) : ℕ :=
  w.leftMass * w.rightMass + w.dominationSlack

def ConvolutionWindow.ready (w : ConvolutionWindow) : Prop :=
  w.convolutionMass ≤ w.massBudget

def ConvolutionWindow.nonzeroIndexBudget (w : ConvolutionWindow) : Prop :=
  w.index ≤ w.index + w.dominationSlack

def ConvolutionWindow.certificate (w : ConvolutionWindow) : ℕ :=
  w.index + w.leftMass + w.rightMass + w.convolutionMass + w.dominationSlack

theorem convolutionMass_le_certificate (w : ConvolutionWindow) :
    w.convolutionMass ≤ w.certificate := by
  unfold ConvolutionWindow.certificate
  omega

def sampleConvolutionWindow : ConvolutionWindow :=
  { index := 1, leftMass := 5, rightMass := 5, convolutionMass := 12, dominationSlack := 0 }

example : sampleConvolutionWindow.ready := by
  norm_num [sampleConvolutionWindow, ConvolutionWindow.ready, ConvolutionWindow.massBudget]

structure ConvolutionRefinementWindow where
  indexWindow : ℕ
  leftWindow : ℕ
  rightWindow : ℕ
  convolutionWindow : ℕ
  refinementBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ConvolutionRefinementWindow.convolutionControlled
    (w : ConvolutionRefinementWindow) : Prop :=
  w.convolutionWindow ≤ w.leftWindow * w.rightWindow + w.slack

def convolutionRefinementWindowReady (w : ConvolutionRefinementWindow) : Prop :=
  w.convolutionControlled ∧
    w.refinementBudget ≤ w.indexWindow + w.convolutionWindow + w.slack

def ConvolutionRefinementWindow.certificate
    (w : ConvolutionRefinementWindow) : ℕ :=
  w.indexWindow + w.leftWindow + w.rightWindow + w.convolutionWindow + w.refinementBudget + w.slack

theorem convolutionRefinement_budget_le_certificate
    (w : ConvolutionRefinementWindow) :
    w.refinementBudget ≤ w.certificate := by
  unfold ConvolutionRefinementWindow.certificate
  omega

def sampleConvolutionRefinementWindow : ConvolutionRefinementWindow :=
  { indexWindow := 1, leftWindow := 5, rightWindow := 5, convolutionWindow := 12,
    refinementBudget := 13, slack := 0 }

example : convolutionRefinementWindowReady sampleConvolutionRefinementWindow := by
  norm_num [convolutionRefinementWindowReady,
    ConvolutionRefinementWindow.convolutionControlled, sampleConvolutionRefinementWindow]


structure ConvolutionTauberianSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ConvolutionTauberianSchemasBudgetCertificate.controlled
    (c : ConvolutionTauberianSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def ConvolutionTauberianSchemasBudgetCertificate.budgetControlled
    (c : ConvolutionTauberianSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def ConvolutionTauberianSchemasBudgetCertificate.Ready
    (c : ConvolutionTauberianSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ConvolutionTauberianSchemasBudgetCertificate.size
    (c : ConvolutionTauberianSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem convolutionTauberianSchemas_budgetCertificate_le_size
    (c : ConvolutionTauberianSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleConvolutionTauberianSchemasBudgetCertificate :
    ConvolutionTauberianSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleConvolutionTauberianSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [ConvolutionTauberianSchemasBudgetCertificate.controlled,
      sampleConvolutionTauberianSchemasBudgetCertificate]
  · norm_num [ConvolutionTauberianSchemasBudgetCertificate.budgetControlled,
      sampleConvolutionTauberianSchemasBudgetCertificate]

example :
    sampleConvolutionTauberianSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleConvolutionTauberianSchemasBudgetCertificate.size := by
  apply convolutionTauberianSchemas_budgetCertificate_le_size
  constructor
  · norm_num [ConvolutionTauberianSchemasBudgetCertificate.controlled,
      sampleConvolutionTauberianSchemasBudgetCertificate]
  · norm_num [ConvolutionTauberianSchemasBudgetCertificate.budgetControlled,
      sampleConvolutionTauberianSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleConvolutionTauberianSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [ConvolutionTauberianSchemasBudgetCertificate.controlled,
      sampleConvolutionTauberianSchemasBudgetCertificate]
  · norm_num [ConvolutionTauberianSchemasBudgetCertificate.budgetControlled,
      sampleConvolutionTauberianSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleConvolutionTauberianSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleConvolutionTauberianSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List ConvolutionTauberianSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleConvolutionTauberianSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleConvolutionTauberianSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.ConvolutionTauberianSchemas
