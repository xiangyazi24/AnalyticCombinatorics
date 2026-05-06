import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Darboux asymptotics.
-/

namespace AnalyticCombinatorics.Asymptotics.DarbouxAsymptotics

/-- First forward difference over integer-valued coefficient samples. -/
def firstDifferenceZ (a : ℕ → ℤ) (n : ℕ) : ℤ :=
  a (n + 1) - a n

/-- Second forward difference over integer-valued coefficient samples. -/
def secondDifferenceZ (a : ℕ → ℤ) (n : ℕ) : ℤ :=
  a (n + 2) - 2 * a (n + 1) + a n

/-- Finite Darboux polynomial tail certificate by bounded second difference. -/
def secondDifferenceBoundedUpTo
    (a : ℕ → ℤ) (bound N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    secondDifferenceZ a n ≤ (bound : ℤ) ∧
      -((bound : ℤ)) ≤ secondDifferenceZ a n

def linearTailModel (n : ℕ) : ℤ :=
  n + 1

def quadraticTailModel (n : ℕ) : ℤ :=
  (n + 1) ^ 2

theorem linearTail_secondDifference_zero :
    ∀ n : Fin 16, secondDifferenceZ linearTailModel n.val = 0 := by
  native_decide

theorem quadraticTail_secondDifference_two :
    ∀ n : Fin 16, secondDifferenceZ quadraticTailModel n.val = 2 := by
  native_decide

theorem quadraticTail_darbouxWindow :
    secondDifferenceBoundedUpTo quadraticTailModel 2 16 = true := by
  unfold secondDifferenceBoundedUpTo secondDifferenceZ quadraticTailModel
  native_decide

example : firstDifferenceZ quadraticTailModel 3 = 9 := by
  unfold firstDifferenceZ quadraticTailModel
  native_decide

example : secondDifferenceZ quadraticTailModel 7 = 2 := by
  native_decide

structure DarbouxAsymptoticsBudgetCertificate where
  boundaryWindow : ℕ
  expansionWindow : ℕ
  coefficientWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DarbouxAsymptoticsBudgetCertificate.controlled
    (c : DarbouxAsymptoticsBudgetCertificate) : Prop :=
  0 < c.boundaryWindow ∧
    c.coefficientWindow ≤ c.boundaryWindow + c.expansionWindow + c.slack

def DarbouxAsymptoticsBudgetCertificate.budgetControlled
    (c : DarbouxAsymptoticsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.boundaryWindow + c.expansionWindow + c.coefficientWindow + c.slack

def DarbouxAsymptoticsBudgetCertificate.Ready
    (c : DarbouxAsymptoticsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def DarbouxAsymptoticsBudgetCertificate.size
    (c : DarbouxAsymptoticsBudgetCertificate) : ℕ :=
  c.boundaryWindow + c.expansionWindow + c.coefficientWindow + c.slack

theorem darbouxAsymptotics_budgetCertificate_le_size
    (c : DarbouxAsymptoticsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleDarbouxAsymptoticsBudgetCertificate :
    DarbouxAsymptoticsBudgetCertificate :=
  { boundaryWindow := 5
    expansionWindow := 6
    coefficientWindow := 10
    certificateBudgetWindow := 22
    slack := 1 }

/-- Finite executable readiness audit for Darboux budget certificates. -/
def darbouxAsymptoticsListReady
    (certs : List DarbouxAsymptoticsBudgetCertificate) : Bool :=
  certs.all fun c =>
    0 < c.boundaryWindow &&
      c.coefficientWindow ≤ c.boundaryWindow + c.expansionWindow + c.slack &&
        c.certificateBudgetWindow ≤
          c.boundaryWindow + c.expansionWindow + c.coefficientWindow + c.slack

theorem darbouxAsymptoticsList_readyWindow :
    darbouxAsymptoticsListReady
      [{ boundaryWindow := 3, expansionWindow := 4, coefficientWindow := 6,
         certificateBudgetWindow := 13, slack := 0 },
       { boundaryWindow := 5, expansionWindow := 6, coefficientWindow := 10,
         certificateBudgetWindow := 22, slack := 1 }] = true := by
  unfold darbouxAsymptoticsListReady
  native_decide

example : sampleDarbouxAsymptoticsBudgetCertificate.Ready := by
  constructor
  · norm_num [DarbouxAsymptoticsBudgetCertificate.controlled,
      sampleDarbouxAsymptoticsBudgetCertificate]
  · norm_num [DarbouxAsymptoticsBudgetCertificate.budgetControlled,
      sampleDarbouxAsymptoticsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleDarbouxAsymptoticsBudgetCertificate.Ready := by
  constructor
  · norm_num [DarbouxAsymptoticsBudgetCertificate.controlled,
      sampleDarbouxAsymptoticsBudgetCertificate]
  · norm_num [DarbouxAsymptoticsBudgetCertificate.budgetControlled,
      sampleDarbouxAsymptoticsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleDarbouxAsymptoticsBudgetCertificate.certificateBudgetWindow ≤
      sampleDarbouxAsymptoticsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List DarbouxAsymptoticsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleDarbouxAsymptoticsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleDarbouxAsymptoticsBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.DarbouxAsymptotics
