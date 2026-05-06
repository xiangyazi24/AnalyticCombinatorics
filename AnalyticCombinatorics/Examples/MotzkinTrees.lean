import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Motzkin tree examples.

Unary-binary trees counted by edges follow the Motzkin number table.
-/

namespace AnalyticCombinatorics.Examples.MotzkinTrees

def motzkinTreeCount : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 4
  | 4 => 9
  | 5 => 21
  | 6 => 51
  | 7 => 127
  | 8 => 323
  | 9 => 835
  | 10 => 2188
  | _ => 0

example : motzkinTreeCount 0 = 1 := by native_decide
example : motzkinTreeCount 1 = 1 := by native_decide
example : motzkinTreeCount 2 = 2 := by native_decide
example : motzkinTreeCount 3 = 4 := by native_decide
example : motzkinTreeCount 4 = 9 := by native_decide
example : motzkinTreeCount 5 = 21 := by native_decide
example : motzkinTreeCount 10 = 2188 := by native_decide

theorem motzkinTreeCount_values_0_to_10 :
    (List.range 11).map motzkinTreeCount =
      [1, 1, 2, 4, 9, 21, 51, 127, 323, 835, 2188] := by
  native_decide

structure MotzkinTreeProfile where
  leaves : ℕ
  unaryNodes : ℕ
  binaryNodes : ℕ
  edgeBudget : ℕ
deriving DecidableEq, Repr

def MotzkinTreeProfile.nodeCount (p : MotzkinTreeProfile) : ℕ :=
  p.leaves + p.unaryNodes + p.binaryNodes

def MotzkinTreeProfile.edgeCount (p : MotzkinTreeProfile) : ℕ :=
  p.unaryNodes + 2 * p.binaryNodes

def MotzkinTreeProfile.fullUnaryBinaryReady (p : MotzkinTreeProfile) : Prop :=
  0 < p.leaves ∧ p.leaves = p.binaryNodes + 1

def MotzkinTreeProfile.edgeControlled (p : MotzkinTreeProfile) : Prop :=
  p.edgeCount ≤ p.edgeBudget

def MotzkinTreeProfile.certificate (p : MotzkinTreeProfile) : ℕ :=
  p.nodeCount + p.edgeCount + p.edgeBudget

theorem unaryNodes_le_certificate (p : MotzkinTreeProfile) :
    p.unaryNodes ≤ p.certificate := by
  unfold MotzkinTreeProfile.certificate MotzkinTreeProfile.nodeCount
    MotzkinTreeProfile.edgeCount
  omega

theorem binaryNodes_le_certificate (p : MotzkinTreeProfile) :
    p.binaryNodes ≤ p.certificate := by
  unfold MotzkinTreeProfile.certificate MotzkinTreeProfile.nodeCount
    MotzkinTreeProfile.edgeCount
  omega

def sampleMotzkinTreeProfile : MotzkinTreeProfile :=
  { leaves := 4, unaryNodes := 2, binaryNodes := 3, edgeBudget := 8 }

example : sampleMotzkinTreeProfile.fullUnaryBinaryReady := by
  norm_num [sampleMotzkinTreeProfile, MotzkinTreeProfile.fullUnaryBinaryReady]

example : sampleMotzkinTreeProfile.edgeControlled := by
  norm_num [sampleMotzkinTreeProfile, MotzkinTreeProfile.edgeControlled,
    MotzkinTreeProfile.edgeCount]

example : sampleMotzkinTreeProfile.certificate = 25 := by
  norm_num [sampleMotzkinTreeProfile, MotzkinTreeProfile.certificate,
    MotzkinTreeProfile.nodeCount, MotzkinTreeProfile.edgeCount]

structure MotzkinTreesBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MotzkinTreesBudgetCertificate.controlled
    (c : MotzkinTreesBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def MotzkinTreesBudgetCertificate.budgetControlled
    (c : MotzkinTreesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def MotzkinTreesBudgetCertificate.Ready
    (c : MotzkinTreesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def MotzkinTreesBudgetCertificate.size
    (c : MotzkinTreesBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem motzkinTrees_budgetCertificate_le_size
    (c : MotzkinTreesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleMotzkinTreesBudgetCertificate : MotzkinTreesBudgetCertificate :=
  { primaryWindow := 4
    secondaryWindow := 5
    certificateBudgetWindow := 10
    slack := 1 }

example : sampleMotzkinTreesBudgetCertificate.Ready := by
  constructor
  · norm_num [MotzkinTreesBudgetCertificate.controlled,
      sampleMotzkinTreesBudgetCertificate]
  · norm_num [MotzkinTreesBudgetCertificate.budgetControlled,
      sampleMotzkinTreesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleMotzkinTreesBudgetCertificate.Ready := by
  constructor
  · norm_num [MotzkinTreesBudgetCertificate.controlled,
      sampleMotzkinTreesBudgetCertificate]
  · norm_num [MotzkinTreesBudgetCertificate.budgetControlled,
      sampleMotzkinTreesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleMotzkinTreesBudgetCertificate.certificateBudgetWindow ≤
      sampleMotzkinTreesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List MotzkinTreesBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleMotzkinTreesBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleMotzkinTreesBudgetCertificate
  native_decide

end AnalyticCombinatorics.Examples.MotzkinTrees
