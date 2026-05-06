import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Compositions into even parts.

A composition of `2m` into positive even parts is the same as a composition of
`m` into positive parts. Odd totals have no such compositions.
-/

namespace AnalyticCombinatorics.Examples.CompositionsEven

/-- Count of compositions of `n` into positive even parts. -/
def evenCompositionCount (n : ℕ) : ℕ :=
  if n = 0 then 1
  else if n % 2 = 0 then 2 ^ (n / 2 - 1)
  else 0

example : evenCompositionCount 0 = 1 := by native_decide
example : evenCompositionCount 1 = 0 := by native_decide
example : evenCompositionCount 2 = 1 := by native_decide
example : evenCompositionCount 3 = 0 := by native_decide
example : evenCompositionCount 4 = 2 := by native_decide
example : evenCompositionCount 5 = 0 := by native_decide
example : evenCompositionCount 6 = 4 := by native_decide
example : evenCompositionCount 7 = 0 := by native_decide
example : evenCompositionCount 8 = 8 := by native_decide
example : evenCompositionCount 9 = 0 := by native_decide
example : evenCompositionCount 10 = 16 := by native_decide

theorem evenCompositionCount_odd_upto_11 :
    (List.range 6).all
      (fun k => evenCompositionCount (2 * k + 1) == 0) = true := by
  native_decide

theorem evenCompositionCount_even_upto_10 :
    (List.range 6).all
      (fun k =>
        evenCompositionCount (2 * k) ==
          if k = 0 then 1 else 2 ^ (k - 1)) = true := by
  native_decide

structure EvenCompositionWindow where
  total : ℕ
  halfTotal : ℕ
  parts : ℕ
  maxHalfPart : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def EvenCompositionWindow.parityReady (w : EvenCompositionWindow) : Prop :=
  w.total = 2 * w.halfTotal

def EvenCompositionWindow.sizeControlled (w : EvenCompositionWindow) : Prop :=
  w.halfTotal ≤ w.parts * w.maxHalfPart + w.slack

def EvenCompositionWindow.ready (w : EvenCompositionWindow) : Prop :=
  w.parityReady ∧ w.sizeControlled

def EvenCompositionWindow.certificate (w : EvenCompositionWindow) : ℕ :=
  w.total + w.halfTotal + w.parts + w.maxHalfPart + w.slack

theorem halfTotal_le_certificate (w : EvenCompositionWindow) :
    w.halfTotal ≤ w.certificate := by
  unfold EvenCompositionWindow.certificate
  omega

def sampleEvenCompositionWindow : EvenCompositionWindow :=
  { total := 10, halfTotal := 5, parts := 2, maxHalfPart := 3, slack := 0 }

example : sampleEvenCompositionWindow.ready := by
  norm_num [sampleEvenCompositionWindow, EvenCompositionWindow.ready,
    EvenCompositionWindow.parityReady, EvenCompositionWindow.sizeControlled]

structure CompositionsEvenBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CompositionsEvenBudgetCertificate.controlled
    (c : CompositionsEvenBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def CompositionsEvenBudgetCertificate.budgetControlled
    (c : CompositionsEvenBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def CompositionsEvenBudgetCertificate.Ready
    (c : CompositionsEvenBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CompositionsEvenBudgetCertificate.size
    (c : CompositionsEvenBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem compositionsEven_budgetCertificate_le_size
    (c : CompositionsEvenBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleCompositionsEvenBudgetCertificate :
    CompositionsEvenBudgetCertificate :=
  { primaryWindow := 4
    secondaryWindow := 5
    certificateBudgetWindow := 10
    slack := 1 }

example : sampleCompositionsEvenBudgetCertificate.Ready := by
  constructor
  · norm_num [CompositionsEvenBudgetCertificate.controlled,
      sampleCompositionsEvenBudgetCertificate]
  · norm_num [CompositionsEvenBudgetCertificate.budgetControlled,
      sampleCompositionsEvenBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleCompositionsEvenBudgetCertificate.Ready := by
  constructor
  · norm_num [CompositionsEvenBudgetCertificate.controlled,
      sampleCompositionsEvenBudgetCertificate]
  · norm_num [CompositionsEvenBudgetCertificate.budgetControlled,
      sampleCompositionsEvenBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCompositionsEvenBudgetCertificate.certificateBudgetWindow ≤
      sampleCompositionsEvenBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List CompositionsEvenBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCompositionsEvenBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleCompositionsEvenBudgetCertificate
  native_decide

end AnalyticCombinatorics.Examples.CompositionsEven
