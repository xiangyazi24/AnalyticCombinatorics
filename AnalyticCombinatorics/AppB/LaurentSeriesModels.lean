import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Laurent principal-part bookkeeping.

The module records finite information about pole orders and coefficients
without importing any analytic series infrastructure.
-/

namespace AnalyticCombinatorics.AppB.LaurentSeriesModels

structure PrincipalTerm where
  order : ℕ
  coeffMagnitude : ℕ
deriving DecidableEq, Repr

def termWeight (t : PrincipalTerm) : ℕ :=
  t.order * t.coeffMagnitude

def principalWeight (terms : List PrincipalTerm) : ℕ :=
  terms.map termWeight |>.sum

def nonzeroPrincipalTerm (t : PrincipalTerm) : Prop :=
  0 < t.order ∧ 0 < t.coeffMagnitude

theorem termWeight_positive {t : PrincipalTerm}
    (h : nonzeroPrincipalTerm t) :
    0 < termWeight t := by
  unfold nonzeroPrincipalTerm termWeight at *
  exact Nat.mul_pos h.1 h.2

theorem principalWeight_cons (t : PrincipalTerm) (ts : List PrincipalTerm) :
    principalWeight (t :: ts) = termWeight t + principalWeight ts := by
  simp [principalWeight]

def sampleTerm : PrincipalTerm :=
  { order := 3, coeffMagnitude := 5 }

example : nonzeroPrincipalTerm sampleTerm := by
  norm_num [nonzeroPrincipalTerm, sampleTerm]

example : termWeight sampleTerm = 15 := by
  native_decide

example : principalWeight [sampleTerm, { order := 1, coeffMagnitude := 2 }] = 17 := by
  native_decide

structure LaurentWindow where
  poleOrder : ℕ
  principalTerms : ℕ
  coefficientMass : ℕ
  regularPartBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LaurentWindow.poleReady (w : LaurentWindow) : Prop :=
  0 < w.poleOrder

def LaurentWindow.principalControlled (w : LaurentWindow) : Prop :=
  w.principalTerms ≤ w.poleOrder + w.slack

def LaurentWindow.coefficientControlled (w : LaurentWindow) : Prop :=
  w.coefficientMass ≤ w.regularPartBudget + w.slack

def LaurentWindow.ready (w : LaurentWindow) : Prop :=
  w.poleReady ∧ w.principalControlled ∧ w.coefficientControlled

def LaurentWindow.certificate (w : LaurentWindow) : ℕ :=
  w.poleOrder + w.principalTerms + w.coefficientMass + w.regularPartBudget + w.slack

theorem coefficientMass_le_certificate (w : LaurentWindow) :
    w.coefficientMass ≤ w.certificate := by
  unfold LaurentWindow.certificate
  omega

def sampleLaurentWindow : LaurentWindow :=
  { poleOrder := 3, principalTerms := 2, coefficientMass := 17,
    regularPartBudget := 20, slack := 0 }

example : sampleLaurentWindow.ready := by
  norm_num [sampleLaurentWindow, LaurentWindow.ready, LaurentWindow.poleReady,
    LaurentWindow.principalControlled, LaurentWindow.coefficientControlled]


structure LaurentSeriesModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LaurentSeriesModelsBudgetCertificate.controlled
    (c : LaurentSeriesModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def LaurentSeriesModelsBudgetCertificate.budgetControlled
    (c : LaurentSeriesModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def LaurentSeriesModelsBudgetCertificate.Ready
    (c : LaurentSeriesModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LaurentSeriesModelsBudgetCertificate.size
    (c : LaurentSeriesModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem laurentSeriesModels_budgetCertificate_le_size
    (c : LaurentSeriesModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleLaurentSeriesModelsBudgetCertificate :
    LaurentSeriesModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleLaurentSeriesModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [LaurentSeriesModelsBudgetCertificate.controlled,
      sampleLaurentSeriesModelsBudgetCertificate]
  · norm_num [LaurentSeriesModelsBudgetCertificate.budgetControlled,
      sampleLaurentSeriesModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleLaurentSeriesModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleLaurentSeriesModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleLaurentSeriesModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [LaurentSeriesModelsBudgetCertificate.controlled,
      sampleLaurentSeriesModelsBudgetCertificate]
  · norm_num [LaurentSeriesModelsBudgetCertificate.budgetControlled,
      sampleLaurentSeriesModelsBudgetCertificate]

example :
    sampleLaurentSeriesModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleLaurentSeriesModelsBudgetCertificate.size := by
  apply laurentSeriesModels_budgetCertificate_le_size
  constructor
  · norm_num [LaurentSeriesModelsBudgetCertificate.controlled,
      sampleLaurentSeriesModelsBudgetCertificate]
  · norm_num [LaurentSeriesModelsBudgetCertificate.budgetControlled,
      sampleLaurentSeriesModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List LaurentSeriesModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleLaurentSeriesModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleLaurentSeriesModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.LaurentSeriesModels
