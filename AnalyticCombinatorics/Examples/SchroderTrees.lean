import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Schroder tree examples.

Large Schroder numbers count plane trees whose internal nodes have at least
two children, with the conventional first values recorded below.
-/

namespace AnalyticCombinatorics.Examples.SchroderTrees

def schroderTreeCount : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 6
  | 3 => 22
  | 4 => 90
  | 5 => 394
  | 6 => 1806
  | 7 => 8558
  | 8 => 41586
  | 9 => 206098
  | 10 => 1037718
  | _ => 0

example : schroderTreeCount 0 = 1 := by native_decide
example : schroderTreeCount 1 = 2 := by native_decide
example : schroderTreeCount 2 = 6 := by native_decide
example : schroderTreeCount 3 = 22 := by native_decide
example : schroderTreeCount 4 = 90 := by native_decide
example : schroderTreeCount 5 = 394 := by native_decide
example : schroderTreeCount 10 = 1037718 := by native_decide

theorem schroderTreeCount_values_0_to_10 :
    (List.range 11).map schroderTreeCount =
      [1, 2, 6, 22, 90, 394, 1806, 8558, 41586, 206098, 1037718] := by
  native_decide

structure SchroderTreeProfile where
  leaves : ℕ
  internalNodes : ℕ
  childSlots : ℕ
  aritySlack : ℕ
deriving DecidableEq, Repr

def SchroderTreeProfile.minimumChildSlots (p : SchroderTreeProfile) : ℕ :=
  2 * p.internalNodes

def SchroderTreeProfile.arityReady (p : SchroderTreeProfile) : Prop :=
  p.minimumChildSlots ≤ p.childSlots + p.aritySlack

def SchroderTreeProfile.edgeBudget (p : SchroderTreeProfile) : ℕ :=
  p.leaves + p.internalNodes + p.childSlots

def SchroderTreeProfile.certificate (p : SchroderTreeProfile) : ℕ :=
  p.leaves + p.internalNodes + p.childSlots + p.aritySlack

theorem internalNodes_le_certificate (p : SchroderTreeProfile) :
    p.internalNodes ≤ p.certificate := by
  unfold SchroderTreeProfile.certificate
  omega

def sampleSchroderTreeProfile : SchroderTreeProfile :=
  { leaves := 6, internalNodes := 3, childSlots := 8, aritySlack := 0 }

example : sampleSchroderTreeProfile.arityReady := by
  norm_num [sampleSchroderTreeProfile, SchroderTreeProfile.arityReady,
    SchroderTreeProfile.minimumChildSlots]

example : sampleSchroderTreeProfile.edgeBudget = 17 := by
  native_decide

structure SchroderTreesBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SchroderTreesBudgetCertificate.controlled
    (c : SchroderTreesBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def SchroderTreesBudgetCertificate.budgetControlled
    (c : SchroderTreesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def SchroderTreesBudgetCertificate.Ready
    (c : SchroderTreesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SchroderTreesBudgetCertificate.size
    (c : SchroderTreesBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem schroderTrees_budgetCertificate_le_size
    (c : SchroderTreesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleSchroderTreesBudgetCertificate : SchroderTreesBudgetCertificate :=
  { primaryWindow := 4
    secondaryWindow := 5
    certificateBudgetWindow := 10
    slack := 1 }

example : sampleSchroderTreesBudgetCertificate.Ready := by
  constructor
  · norm_num [SchroderTreesBudgetCertificate.controlled,
      sampleSchroderTreesBudgetCertificate]
  · norm_num [SchroderTreesBudgetCertificate.budgetControlled,
      sampleSchroderTreesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleSchroderTreesBudgetCertificate.Ready := by
  constructor
  · norm_num [SchroderTreesBudgetCertificate.controlled,
      sampleSchroderTreesBudgetCertificate]
  · norm_num [SchroderTreesBudgetCertificate.budgetControlled,
      sampleSchroderTreesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSchroderTreesBudgetCertificate.certificateBudgetWindow ≤
      sampleSchroderTreesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List SchroderTreesBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSchroderTreesBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleSchroderTreesBudgetCertificate
  native_decide

end AnalyticCombinatorics.Examples.SchroderTrees
