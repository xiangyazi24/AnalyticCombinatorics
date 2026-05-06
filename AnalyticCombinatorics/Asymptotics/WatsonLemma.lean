import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Watson lemma

Finite coefficient, factorial-moment, and Laplace-window models for Watson's
lemma.
-/

namespace AnalyticCombinatorics.Asymptotics.WatsonLemma

/-- Factorial moments used by the elementary Laplace model. -/
def factorialMoment : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * factorialMoment n

theorem factorialMoment_samples :
    (List.range 7).map factorialMoment = [1, 1, 2, 6, 24, 120, 720] := by
  native_decide

/-- Finite Watson coefficient contribution `a_k k! / x^{k+1}`. -/
def watsonTerm (coeff : ℚ) (k x : ℕ) : ℚ :=
  coeff * (factorialMoment k : ℚ) / ((x : ℚ) ^ (k + 1))

theorem watsonTerm_samples :
    watsonTerm 1 0 2 = 1 / 2 ∧
      watsonTerm 3 2 2 = 3 / 4 ∧
        watsonTerm (-1) 3 4 = -3 / 128 := by
  native_decide

/-- A three-term finite Watson expansion certificate. -/
def watsonExpansion3 (a0 a1 a2 : ℚ) (x : ℕ) : ℚ :=
  watsonTerm a0 0 x + watsonTerm a1 1 x + watsonTerm a2 2 x

theorem watsonExpansion3_samples :
    watsonExpansion3 1 1 1 2 = 1 ∧
      watsonExpansion3 2 0 3 3 = 8 / 9 := by
  native_decide

/-- Window data for a Watson-lemma expansion. -/
structure WatsonLemmaWindow where
  expansionOrder : ℕ
  laplaceWindow : ℕ
  coefficientWindow : ℕ
  remainderWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def WatsonLemmaWindow.controlled (w : WatsonLemmaWindow) : Prop :=
  0 < w.expansionOrder ∧
    0 < w.laplaceWindow ∧
      w.remainderWindow ≤ w.expansionOrder + w.coefficientWindow + w.slack

def WatsonLemmaWindow.ready (w : WatsonLemmaWindow) : Prop :=
  w.controlled

def sampleWatsonLemmaWindow : WatsonLemmaWindow :=
  { expansionOrder := 5
    laplaceWindow := 8
    coefficientWindow := 4
    remainderWindow := 10
    slack := 1 }

example : sampleWatsonLemmaWindow.ready := by
  norm_num [WatsonLemmaWindow.ready, WatsonLemmaWindow.controlled,
    sampleWatsonLemmaWindow]

/-- Boolean audit for finite Watson-lemma windows. -/
def watsonLemmaWindowListReady (data : List WatsonLemmaWindow) : Bool :=
  data.all fun w =>
    0 < w.expansionOrder &&
      0 < w.laplaceWindow &&
        w.remainderWindow ≤ w.expansionOrder + w.coefficientWindow + w.slack

theorem watsonLemmaWindowList_readyWindow :
    watsonLemmaWindowListReady
      [sampleWatsonLemmaWindow,
       { expansionOrder := 3, laplaceWindow := 4, coefficientWindow := 2,
         remainderWindow := 5, slack := 0 }] = true := by
  unfold watsonLemmaWindowListReady sampleWatsonLemmaWindow
  native_decide

/-- Budget certificate for a finite Watson-lemma proof. -/
structure WatsonLemmaBudgetCertificate where
  expansionWindow : ℕ
  laplaceWindow : ℕ
  coefficientWindow : ℕ
  remainderWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def WatsonLemmaBudgetCertificate.controlled
    (c : WatsonLemmaBudgetCertificate) : Prop :=
  0 < c.expansionWindow ∧
    0 < c.laplaceWindow ∧
      c.remainderWindow ≤ c.expansionWindow + c.coefficientWindow + c.slack

def WatsonLemmaBudgetCertificate.budgetControlled
    (c : WatsonLemmaBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.expansionWindow + c.laplaceWindow + c.coefficientWindow +
      c.remainderWindow + c.slack

def WatsonLemmaBudgetCertificate.Ready
    (c : WatsonLemmaBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def WatsonLemmaBudgetCertificate.size
    (c : WatsonLemmaBudgetCertificate) : ℕ :=
  c.expansionWindow + c.laplaceWindow + c.coefficientWindow +
    c.remainderWindow + c.slack

theorem watsonLemma_budgetCertificate_le_size
    (c : WatsonLemmaBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleWatsonLemmaBudgetCertificate :
    WatsonLemmaBudgetCertificate :=
  { expansionWindow := 5
    laplaceWindow := 8
    coefficientWindow := 4
    remainderWindow := 10
    certificateBudgetWindow := 28
    slack := 1 }

example : sampleWatsonLemmaBudgetCertificate.Ready := by
  constructor
  · norm_num [WatsonLemmaBudgetCertificate.controlled,
      sampleWatsonLemmaBudgetCertificate]
  · norm_num [WatsonLemmaBudgetCertificate.budgetControlled,
      sampleWatsonLemmaBudgetCertificate]

/-- Finite executable readiness audit for Watson-lemma budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleWatsonLemmaBudgetCertificate.Ready := by
  constructor
  · norm_num [WatsonLemmaBudgetCertificate.controlled,
      sampleWatsonLemmaBudgetCertificate]
  · norm_num [WatsonLemmaBudgetCertificate.budgetControlled,
      sampleWatsonLemmaBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleWatsonLemmaBudgetCertificate.certificateBudgetWindow ≤
      sampleWatsonLemmaBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List WatsonLemmaBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleWatsonLemmaBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleWatsonLemmaBudgetCertificate
  native_decide

end AnalyticCombinatorics.Asymptotics.WatsonLemma
