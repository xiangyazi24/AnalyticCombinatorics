import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite word metrics for list-encoded words.

These definitions support small checks for languages, pattern avoidance, and
digital combinatorics.
-/

namespace AnalyticCombinatorics.AppA.FiniteWordMetrics

def hammingMismatchCount (xs ys : List ℕ) : ℕ :=
  (xs.zip ys).filter (fun pair => pair.1 != pair.2) |>.length

def prefixLength (xs ys : List ℕ) : ℕ :=
  (xs.zip ys).takeWhile (fun pair => pair.1 == pair.2) |>.length

def wordLength (xs : List ℕ) : ℕ :=
  xs.length

theorem hammingMismatchCount_nil_left (ys : List ℕ) :
    hammingMismatchCount [] ys = 0 := by
  simp [hammingMismatchCount]

theorem hammingMismatchCount_nil_right (xs : List ℕ) :
    hammingMismatchCount xs [] = 0 := by
  cases xs <;> simp [hammingMismatchCount]

theorem wordLength_cons (x : ℕ) (xs : List ℕ) :
    wordLength (x :: xs) = wordLength xs + 1 := by
  simp [wordLength]

example : hammingMismatchCount [0, 1, 1, 0] [0, 0, 1, 1] = 2 := by
  native_decide

example : prefixLength [1, 2, 3] [1, 2, 4] = 2 := by
  native_decide

example : wordLength [3, 1, 4, 1, 5] = 5 := by
  native_decide

structure WordMetricWindow where
  length : ℕ
  prefixAgreement : ℕ
  hammingDistance : ℕ
  alphabetSize : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def WordMetricWindow.prefixControlled (w : WordMetricWindow) : Prop :=
  w.prefixAgreement ≤ w.length

def WordMetricWindow.distanceControlled (w : WordMetricWindow) : Prop :=
  w.hammingDistance ≤ w.length + w.slack

def WordMetricWindow.nonemptyAlphabet (w : WordMetricWindow) : Prop :=
  0 < w.alphabetSize

def WordMetricWindow.ready (w : WordMetricWindow) : Prop :=
  w.prefixControlled ∧ w.distanceControlled ∧ w.nonemptyAlphabet

def WordMetricWindow.certificate (w : WordMetricWindow) : ℕ :=
  w.length + w.prefixAgreement + w.hammingDistance + w.alphabetSize + w.slack

theorem hammingDistance_le_certificate (w : WordMetricWindow) :
    w.hammingDistance ≤ w.certificate := by
  unfold WordMetricWindow.certificate
  omega

def sampleWordMetricWindow : WordMetricWindow :=
  { length := 4, prefixAgreement := 2, hammingDistance := 2, alphabetSize := 2, slack := 0 }

example : sampleWordMetricWindow.ready := by
  norm_num [sampleWordMetricWindow, WordMetricWindow.ready, WordMetricWindow.prefixControlled,
    WordMetricWindow.distanceControlled, WordMetricWindow.nonemptyAlphabet]


structure FiniteWordMetricsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteWordMetricsBudgetCertificate.controlled
    (c : FiniteWordMetricsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteWordMetricsBudgetCertificate.budgetControlled
    (c : FiniteWordMetricsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteWordMetricsBudgetCertificate.Ready
    (c : FiniteWordMetricsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteWordMetricsBudgetCertificate.size
    (c : FiniteWordMetricsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteWordMetrics_budgetCertificate_le_size
    (c : FiniteWordMetricsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteWordMetricsBudgetCertificate :
    FiniteWordMetricsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleFiniteWordMetricsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteWordMetricsBudgetCertificate.controlled,
      sampleFiniteWordMetricsBudgetCertificate]
  · norm_num [FiniteWordMetricsBudgetCertificate.budgetControlled,
      sampleFiniteWordMetricsBudgetCertificate]

example :
    sampleFiniteWordMetricsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteWordMetricsBudgetCertificate.size := by
  apply finiteWordMetrics_budgetCertificate_le_size
  constructor
  · norm_num [FiniteWordMetricsBudgetCertificate.controlled,
      sampleFiniteWordMetricsBudgetCertificate]
  · norm_num [FiniteWordMetricsBudgetCertificate.budgetControlled,
      sampleFiniteWordMetricsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleFiniteWordMetricsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteWordMetricsBudgetCertificate.controlled,
      sampleFiniteWordMetricsBudgetCertificate]
  · norm_num [FiniteWordMetricsBudgetCertificate.budgetControlled,
      sampleFiniteWordMetricsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteWordMetricsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteWordMetricsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List FiniteWordMetricsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteWordMetricsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteWordMetricsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteWordMetrics
