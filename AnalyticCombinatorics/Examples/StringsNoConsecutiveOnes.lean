import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Binary strings with no consecutive ones.

The number of length-`n` binary strings avoiding adjacent ones is `F_{n+2}`.
-/

namespace AnalyticCombinatorics.Examples.StringsNoConsecutiveOnes

/-- Count of binary strings of length `n` with no adjacent ones. -/
def noConsecutiveOnesCount : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | n + 2 => noConsecutiveOnesCount (n + 1) + noConsecutiveOnesCount n

theorem noConsecutiveOnesCount_rec (n : ℕ) :
    noConsecutiveOnesCount (n + 2) =
      noConsecutiveOnesCount (n + 1) + noConsecutiveOnesCount n := rfl

example : noConsecutiveOnesCount 0 = 1 := by native_decide
example : noConsecutiveOnesCount 1 = 2 := by native_decide
example : noConsecutiveOnesCount 2 = 3 := by native_decide
example : noConsecutiveOnesCount 3 = 5 := by native_decide
example : noConsecutiveOnesCount 4 = 8 := by native_decide
example : noConsecutiveOnesCount 5 = 13 := by native_decide
example : noConsecutiveOnesCount 6 = 21 := by native_decide
example : noConsecutiveOnesCount 7 = 34 := by native_decide
example : noConsecutiveOnesCount 8 = 55 := by native_decide
example : noConsecutiveOnesCount 9 = 89 := by native_decide
example : noConsecutiveOnesCount 10 = 144 := by native_decide

theorem noConsecutiveOnesCount_eq_fib_upto_10 :
    (List.range 11).all
      (fun n => noConsecutiveOnesCount n == Nat.fib (n + 2)) = true := by
  native_decide

def hasNoConsecutiveOnes : List Bool → Bool
  | [] => true
  | [_] => true
  | true :: true :: _ => false
  | _ :: ys => hasNoConsecutiveOnes ys

def binaryStringsOfLength (n : ℕ) : List (List Bool) :=
  (List.range (2 ^ n)).map (fun k => (List.range n).map (fun i => Nat.testBit k i))

structure BinaryStringAvoidanceWindow where
  length : ℕ
  accepted : ℕ
  rejected : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BinaryStringAvoidanceWindow.totalChecked (w : BinaryStringAvoidanceWindow) : ℕ :=
  w.accepted + w.rejected

def BinaryStringAvoidanceWindow.ready (w : BinaryStringAvoidanceWindow) : Prop :=
  w.accepted = noConsecutiveOnesCount w.length ∧
    w.totalChecked ≤ 2 ^ w.length + w.slack

def BinaryStringAvoidanceWindow.certificate (w : BinaryStringAvoidanceWindow) : ℕ :=
  w.length + w.accepted + w.rejected + w.slack

theorem accepted_le_certificate (w : BinaryStringAvoidanceWindow) :
    w.accepted ≤ w.certificate := by
  unfold BinaryStringAvoidanceWindow.certificate
  omega

def sampleBinaryStringAvoidanceWindow : BinaryStringAvoidanceWindow :=
  { length := 4, accepted := 8, rejected := 8, slack := 0 }

example : hasNoConsecutiveOnes [true, false, true, false] = true := by
  native_decide

example : hasNoConsecutiveOnes [true, true, false] = false := by
  native_decide

example : (binaryStringsOfLength 3).length = 8 := by
  native_decide

example : sampleBinaryStringAvoidanceWindow.ready := by
  norm_num [sampleBinaryStringAvoidanceWindow, BinaryStringAvoidanceWindow.ready,
    BinaryStringAvoidanceWindow.totalChecked, noConsecutiveOnesCount]

structure StringsNoConsecutiveOnesBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def StringsNoConsecutiveOnesBudgetCertificate.controlled
    (c : StringsNoConsecutiveOnesBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def StringsNoConsecutiveOnesBudgetCertificate.budgetControlled
    (c : StringsNoConsecutiveOnesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def StringsNoConsecutiveOnesBudgetCertificate.Ready
    (c : StringsNoConsecutiveOnesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def StringsNoConsecutiveOnesBudgetCertificate.size
    (c : StringsNoConsecutiveOnesBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem stringsNoConsecutiveOnes_budgetCertificate_le_size
    (c : StringsNoConsecutiveOnesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleStringsNoConsecutiveOnesBudgetCertificate :
    StringsNoConsecutiveOnesBudgetCertificate :=
  { primaryWindow := 4
    secondaryWindow := 5
    certificateBudgetWindow := 10
    slack := 1 }

example : sampleStringsNoConsecutiveOnesBudgetCertificate.Ready := by
  constructor
  · norm_num [StringsNoConsecutiveOnesBudgetCertificate.controlled,
      sampleStringsNoConsecutiveOnesBudgetCertificate]
  · norm_num [StringsNoConsecutiveOnesBudgetCertificate.budgetControlled,
      sampleStringsNoConsecutiveOnesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleStringsNoConsecutiveOnesBudgetCertificate.Ready := by
  constructor
  · norm_num [StringsNoConsecutiveOnesBudgetCertificate.controlled,
      sampleStringsNoConsecutiveOnesBudgetCertificate]
  · norm_num [StringsNoConsecutiveOnesBudgetCertificate.budgetControlled,
      sampleStringsNoConsecutiveOnesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleStringsNoConsecutiveOnesBudgetCertificate.certificateBudgetWindow ≤
      sampleStringsNoConsecutiveOnesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List StringsNoConsecutiveOnesBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleStringsNoConsecutiveOnesBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleStringsNoConsecutiveOnesBudgetCertificate
  native_decide

end AnalyticCombinatorics.Examples.StringsNoConsecutiveOnes
