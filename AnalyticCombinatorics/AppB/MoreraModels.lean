import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite Morera-style bookkeeping.

The analytic hypothesis is abstracted as vanishing cycle integrals over a
finite test family; this file records how that condition is transported.
-/

namespace AnalyticCombinatorics.AppB.MoreraModels

structure TriangleTest where
  boundaryIntegralNorm : ℕ
  containedInDomain : Prop
deriving Repr

def integralVanishes (t : TriangleTest) : Prop :=
  t.boundaryIntegralNorm = 0

def moreraTestPassed (tests : List TriangleTest) : Prop :=
  ∀ t ∈ tests, t.containedInDomain ∧ integralVanishes t

def enlargeTestFamily (tests extra : List TriangleTest) : List TriangleTest :=
  tests ++ extra

theorem moreraTestPassed_left {tests extra : List TriangleTest}
    (h : moreraTestPassed (enlargeTestFamily tests extra)) :
    moreraTestPassed tests := by
  intro t ht
  exact h t (by simp [enlargeTestFamily, ht])

theorem integralVanishes_of_zero {t : TriangleTest}
    (h : t.boundaryIntegralNorm = 0) :
    integralVanishes t ∧ t.boundaryIntegralNorm = 0 := by
  exact ⟨h, h⟩

def sampleTest : TriangleTest :=
  { boundaryIntegralNorm := 0, containedInDomain := (0 : ℕ) = 0 }

example : integralVanishes sampleTest := by
  norm_num [integralVanishes, sampleTest]

example : moreraTestPassed [sampleTest] := by
  intro t ht
  simp at ht
  subst t
  norm_num [sampleTest, integralVanishes]

structure MoreraWindow where
  testCount : ℕ
  vanishingTests : ℕ
  boundaryMass : ℕ
  domainSlack : ℕ
deriving DecidableEq, Repr

def MoreraWindow.vanishingControlled (w : MoreraWindow) : Prop :=
  w.vanishingTests ≤ w.testCount

def MoreraWindow.boundaryControlled (w : MoreraWindow) : Prop :=
  w.boundaryMass ≤ w.domainSlack

def MoreraWindow.ready (w : MoreraWindow) : Prop :=
  w.vanishingControlled ∧ w.boundaryControlled

def MoreraWindow.certificate (w : MoreraWindow) : ℕ :=
  w.testCount + w.vanishingTests + w.boundaryMass + w.domainSlack

theorem testCount_le_certificate (w : MoreraWindow) :
    w.testCount ≤ w.certificate := by
  unfold MoreraWindow.certificate
  omega

def sampleMoreraWindow : MoreraWindow :=
  { testCount := 1, vanishingTests := 1, boundaryMass := 0, domainSlack := 0 }

example : sampleMoreraWindow.ready := by
  norm_num [sampleMoreraWindow, MoreraWindow.ready,
    MoreraWindow.vanishingControlled, MoreraWindow.boundaryControlled]


structure MoreraModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MoreraModelsBudgetCertificate.controlled
    (c : MoreraModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def MoreraModelsBudgetCertificate.budgetControlled
    (c : MoreraModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def MoreraModelsBudgetCertificate.Ready
    (c : MoreraModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def MoreraModelsBudgetCertificate.size
    (c : MoreraModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem moreraModels_budgetCertificate_le_size
    (c : MoreraModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleMoreraModelsBudgetCertificate :
    MoreraModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleMoreraModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [MoreraModelsBudgetCertificate.controlled,
      sampleMoreraModelsBudgetCertificate]
  · norm_num [MoreraModelsBudgetCertificate.budgetControlled,
      sampleMoreraModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleMoreraModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleMoreraModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleMoreraModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [MoreraModelsBudgetCertificate.controlled,
      sampleMoreraModelsBudgetCertificate]
  · norm_num [MoreraModelsBudgetCertificate.budgetControlled,
      sampleMoreraModelsBudgetCertificate]

example :
    sampleMoreraModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleMoreraModelsBudgetCertificate.size := by
  apply moreraModels_budgetCertificate_le_size
  constructor
  · norm_num [MoreraModelsBudgetCertificate.controlled,
      sampleMoreraModelsBudgetCertificate]
  · norm_num [MoreraModelsBudgetCertificate.budgetControlled,
      sampleMoreraModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List MoreraModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleMoreraModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleMoreraModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.MoreraModels
