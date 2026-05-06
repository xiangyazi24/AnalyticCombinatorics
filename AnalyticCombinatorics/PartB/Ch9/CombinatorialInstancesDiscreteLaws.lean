import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Combinatorial instances of discrete laws.
-/

namespace AnalyticCombinatorics.PartB.Ch9.CombinatorialInstancesDiscreteLaws

/-- Distribution of fixed points in permutations, sampled by derangement counts. -/
def fixedPointSampleMassNumerator : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 2
  | 4 => 9
  | 5 => 44
  | _ => 0

def factorialSample (n : ℕ) : ℕ :=
  n.factorial

/-- Finite audit that sampled event counts fit inside the ambient class. -/
def combinatorialLawInstanceCheck (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    fixedPointSampleMassNumerator n ≤ factorialSample n

def CombinatorialDiscreteLawWindow (N : ℕ) : Prop :=
  combinatorialLawInstanceCheck N = true

theorem fixedPointSample_window :
    CombinatorialDiscreteLawWindow 5 := by
  unfold CombinatorialDiscreteLawWindow combinatorialLawInstanceCheck
    fixedPointSampleMassNumerator factorialSample
  native_decide

/-- Prefix sum of sampled fixed-point event counts. -/
def fixedPointSamplePrefix (N : ℕ) : ℕ :=
  (List.range (N + 1)).foldl
    (fun total n => total + fixedPointSampleMassNumerator n) 0

def FixedPointSamplePrefixWindow (N total : ℕ) : Prop :=
  fixedPointSamplePrefix N = total

theorem fixedPointSample_prefixWindow :
    FixedPointSamplePrefixWindow 5 58 := by
  unfold FixedPointSamplePrefixWindow fixedPointSamplePrefix
    fixedPointSampleMassNumerator
  native_decide

example : fixedPointSampleMassNumerator 5 = 44 := by
  unfold fixedPointSampleMassNumerator
  native_decide

example : fixedPointSamplePrefix 4 = 14 := by
  unfold fixedPointSamplePrefix fixedPointSampleMassNumerator
  native_decide

structure CombinatorialInstancesDiscreteLawsBudgetCertificate where
  instanceWindow : ℕ
  lawWindow : ℕ
  verificationWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CombinatorialInstancesDiscreteLawsBudgetCertificate.controlled
    (c : CombinatorialInstancesDiscreteLawsBudgetCertificate) : Prop :=
  0 < c.instanceWindow ∧
    c.verificationWindow ≤ c.instanceWindow + c.lawWindow + c.slack

def CombinatorialInstancesDiscreteLawsBudgetCertificate.budgetControlled
    (c : CombinatorialInstancesDiscreteLawsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.instanceWindow + c.lawWindow + c.verificationWindow + c.slack

def CombinatorialInstancesDiscreteLawsBudgetCertificate.Ready
    (c : CombinatorialInstancesDiscreteLawsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CombinatorialInstancesDiscreteLawsBudgetCertificate.size
    (c : CombinatorialInstancesDiscreteLawsBudgetCertificate) : ℕ :=
  c.instanceWindow + c.lawWindow + c.verificationWindow + c.slack

theorem combinatorialInstancesDiscreteLaws_budgetCertificate_le_size
    (c : CombinatorialInstancesDiscreteLawsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleCombinatorialInstancesDiscreteLawsBudgetCertificate :
    CombinatorialInstancesDiscreteLawsBudgetCertificate :=
  { instanceWindow := 5
    lawWindow := 6
    verificationWindow := 10
    certificateBudgetWindow := 22
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleCombinatorialInstancesDiscreteLawsBudgetCertificate.Ready := by
  constructor
  · norm_num [CombinatorialInstancesDiscreteLawsBudgetCertificate.controlled,
      sampleCombinatorialInstancesDiscreteLawsBudgetCertificate]
  · norm_num [CombinatorialInstancesDiscreteLawsBudgetCertificate.budgetControlled,
      sampleCombinatorialInstancesDiscreteLawsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCombinatorialInstancesDiscreteLawsBudgetCertificate.certificateBudgetWindow ≤
      sampleCombinatorialInstancesDiscreteLawsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleCombinatorialInstancesDiscreteLawsBudgetCertificate.Ready := by
  constructor
  · norm_num [CombinatorialInstancesDiscreteLawsBudgetCertificate.controlled,
      sampleCombinatorialInstancesDiscreteLawsBudgetCertificate]
  · norm_num
      [CombinatorialInstancesDiscreteLawsBudgetCertificate.budgetControlled,
        sampleCombinatorialInstancesDiscreteLawsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List CombinatorialInstancesDiscreteLawsBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCombinatorialInstancesDiscreteLawsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleCombinatorialInstancesDiscreteLawsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch9.CombinatorialInstancesDiscreteLaws
