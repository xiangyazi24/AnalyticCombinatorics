import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Combinatorial applications of algebraic functions.

Finite bookkeeping for context-free, walk, and map applications of
algebraic singularity analysis.
-/

namespace AnalyticCombinatorics.PartB.Ch7.CombinatorialApplicationsAlgebraicFunctions

/-- Catalan application of an algebraic function schema. -/
def catalanApplicationCoeff (n : ℕ) : ℕ :=
  (2 * n).choose n / (n + 1)

/-- Finite algebraic-application envelope. -/
def algebraicApplicationEnvelopeCheck (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => catalanApplicationCoeff n ≤ 4 ^ n

theorem catalanApplication_samples :
    catalanApplicationCoeff 0 = 1 ∧
    catalanApplicationCoeff 3 = 5 ∧
    catalanApplicationCoeff 5 = 42 := by
  unfold catalanApplicationCoeff
  native_decide

theorem catalanApplication_envelope :
    algebraicApplicationEnvelopeCheck 16 = true := by
  unfold algebraicApplicationEnvelopeCheck catalanApplicationCoeff
  native_decide

structure AlgebraicApplicationWindow where
  specificationWindow : ℕ
  algebraicSystemWindow : ℕ
  applicationWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def algebraicApplicationReady (w : AlgebraicApplicationWindow) : Prop :=
  0 < w.specificationWindow ∧
    w.applicationWindow ≤
      w.specificationWindow + w.algebraicSystemWindow + w.slack

def algebraicApplicationBudget (w : AlgebraicApplicationWindow) : ℕ :=
  w.specificationWindow + w.algebraicSystemWindow +
    w.applicationWindow + w.slack

theorem applicationWindow_le_algebraicApplicationBudget
    (w : AlgebraicApplicationWindow) :
    w.applicationWindow ≤ algebraicApplicationBudget w := by
  unfold algebraicApplicationBudget
  omega

def sampleAlgebraicApplicationWindow : AlgebraicApplicationWindow :=
  { specificationWindow := 5
    algebraicSystemWindow := 6
    applicationWindow := 10
    slack := 1 }

example : algebraicApplicationReady sampleAlgebraicApplicationWindow := by
  norm_num [algebraicApplicationReady, sampleAlgebraicApplicationWindow]

structure CombinatorialApplicationsAlgebraicFunctionsBudgetCertificate where
  specificationWindow : ℕ
  algebraicWindow : ℕ
  applicationWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CombinatorialApplicationsAlgebraicFunctionsBudgetCertificate.controlled
    (c : CombinatorialApplicationsAlgebraicFunctionsBudgetCertificate) :
    Prop :=
  0 < c.specificationWindow ∧
    c.applicationWindow ≤
      c.specificationWindow + c.algebraicWindow + c.slack

def CombinatorialApplicationsAlgebraicFunctionsBudgetCertificate.budgetControlled
    (c : CombinatorialApplicationsAlgebraicFunctionsBudgetCertificate) :
    Prop :=
  c.certificateBudgetWindow ≤
    c.specificationWindow + c.algebraicWindow + c.applicationWindow + c.slack

def CombinatorialApplicationsAlgebraicFunctionsBudgetCertificate.Ready
    (c : CombinatorialApplicationsAlgebraicFunctionsBudgetCertificate) :
    Prop :=
  c.controlled ∧ c.budgetControlled

def CombinatorialApplicationsAlgebraicFunctionsBudgetCertificate.size
    (c : CombinatorialApplicationsAlgebraicFunctionsBudgetCertificate) : ℕ :=
  c.specificationWindow + c.algebraicWindow + c.applicationWindow + c.slack

theorem combinatorialApplicationsAlgebraicFunctions_budgetCertificate_le_size
    (c : CombinatorialApplicationsAlgebraicFunctionsBudgetCertificate)
    (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleCombinatorialApplicationsAlgebraicFunctionsBudgetCertificate :
    CombinatorialApplicationsAlgebraicFunctionsBudgetCertificate :=
  { specificationWindow := 5
    algebraicWindow := 6
    applicationWindow := 10
    certificateBudgetWindow := 22
    slack := 1 }

example :
    sampleCombinatorialApplicationsAlgebraicFunctionsBudgetCertificate.Ready := by
  constructor
  · norm_num
      [CombinatorialApplicationsAlgebraicFunctionsBudgetCertificate.controlled,
        sampleCombinatorialApplicationsAlgebraicFunctionsBudgetCertificate]
  · norm_num
      [CombinatorialApplicationsAlgebraicFunctionsBudgetCertificate.budgetControlled,
        sampleCombinatorialApplicationsAlgebraicFunctionsBudgetCertificate]

theorem sampleBudgetCertificate_ready :
    sampleCombinatorialApplicationsAlgebraicFunctionsBudgetCertificate.Ready := by
  constructor
  · norm_num [CombinatorialApplicationsAlgebraicFunctionsBudgetCertificate.controlled,
      sampleCombinatorialApplicationsAlgebraicFunctionsBudgetCertificate]
  · norm_num [CombinatorialApplicationsAlgebraicFunctionsBudgetCertificate.budgetControlled,
      sampleCombinatorialApplicationsAlgebraicFunctionsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCombinatorialApplicationsAlgebraicFunctionsBudgetCertificate.certificateBudgetWindow ≤
      sampleCombinatorialApplicationsAlgebraicFunctionsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List CombinatorialApplicationsAlgebraicFunctionsBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCombinatorialApplicationsAlgebraicFunctionsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleCombinatorialApplicationsAlgebraicFunctionsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch7.CombinatorialApplicationsAlgebraicFunctions
