import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform remainder algebra.

This module records finite algebraic rules for combining uniform remainder
budgets.
-/

namespace AnalyticCombinatorics.Asymptotics.UniformRemainderAlgebra

structure RemainderPair where
  first : ℕ
  second : ℕ
deriving DecidableEq, Repr

def combinedRemainder (r : RemainderPair) : ℕ :=
  r.first + r.second

def boundedBy (r : RemainderPair) (budget : ℕ) : Prop :=
  combinedRemainder r ≤ budget

def scaleRemainder (factor : ℕ) (r : RemainderPair) : RemainderPair :=
  { first := factor * r.first, second := factor * r.second }

theorem combinedRemainder_comm (a b : ℕ) :
    combinedRemainder { first := a, second := b } =
      combinedRemainder { first := b, second := a } := by
  change a + b = b + a
  omega

theorem boundedBy_mono {r : RemainderPair} {a b : ℕ}
    (h : boundedBy r a) (hab : a ≤ b) :
    boundedBy r b := by
  unfold boundedBy at *
  omega

def sampleRemainder : RemainderPair :=
  { first := 3, second := 4 }

example : combinedRemainder sampleRemainder = 7 := by
  native_decide

example : boundedBy sampleRemainder 10 := by
  norm_num [boundedBy, combinedRemainder, sampleRemainder]

structure UniformRemainderWindow where
  firstRemainder : ℕ
  secondRemainder : ℕ
  combinedBudget : ℕ
  scaleFactor : ℕ
deriving DecidableEq, Repr

def UniformRemainderWindow.combined (w : UniformRemainderWindow) : ℕ :=
  w.firstRemainder + w.secondRemainder

def UniformRemainderWindow.ready (w : UniformRemainderWindow) : Prop :=
  w.combined ≤ w.combinedBudget

def UniformRemainderWindow.scaledBudget (w : UniformRemainderWindow) : ℕ :=
  w.scaleFactor * w.combinedBudget

def UniformRemainderWindow.certificate (w : UniformRemainderWindow) : ℕ :=
  w.firstRemainder + w.secondRemainder + w.combinedBudget + w.scaleFactor

theorem combinedBudget_le_certificate (w : UniformRemainderWindow) :
    w.combinedBudget ≤ w.certificate := by
  unfold UniformRemainderWindow.certificate
  omega

def sampleUniformRemainderWindow : UniformRemainderWindow :=
  { firstRemainder := 3, secondRemainder := 4, combinedBudget := 10, scaleFactor := 2 }

example : sampleUniformRemainderWindow.ready := by
  norm_num [sampleUniformRemainderWindow, UniformRemainderWindow.ready,
    UniformRemainderWindow.combined]

example : sampleUniformRemainderWindow.scaledBudget = 20 := by
  native_decide

/-- Finite executable readiness audit for uniform remainder windows. -/
def uniformRemainderWindowListReady
    (data : List UniformRemainderWindow) : Bool :=
  data.all fun w => w.firstRemainder + w.secondRemainder ≤ w.combinedBudget

theorem uniformRemainderWindowList_readyWindow :
    uniformRemainderWindowListReady
      [{ firstRemainder := 3, secondRemainder := 4, combinedBudget := 10,
         scaleFactor := 2 },
       { firstRemainder := 2, secondRemainder := 5, combinedBudget := 8,
         scaleFactor := 3 }] = true := by
  unfold uniformRemainderWindowListReady
  native_decide

/-- A refinement certificate for uniform remainder algebra. -/
structure UniformRemainderCertificate where
  firstWindow : ℕ
  secondWindow : ℕ
  combinedWindow : ℕ
  scaleWindow : ℕ
  slack : ℕ

/-- Combined remainder absorbs the two component remainders. -/
def uniformRemainderCertificateControlled
    (w : UniformRemainderCertificate) : Prop :=
  w.firstWindow + w.secondWindow ≤ w.combinedWindow + w.slack

/-- Readiness for a uniform remainder certificate. -/
def uniformRemainderCertificateReady
    (w : UniformRemainderCertificate) : Prop :=
  uniformRemainderCertificateControlled w ∧
    w.combinedWindow ≤ w.firstWindow + w.secondWindow + w.combinedWindow + w.scaleWindow + w.slack

/-- Total size of a uniform remainder certificate. -/
def uniformRemainderCertificateSize
    (w : UniformRemainderCertificate) : ℕ :=
  w.firstWindow + w.secondWindow + w.combinedWindow + w.scaleWindow + w.slack

theorem uniformRemainderCertificate_combined_le_size
    (w : UniformRemainderCertificate)
    (h : uniformRemainderCertificateReady w) :
    w.combinedWindow ≤ uniformRemainderCertificateSize w := by
  rcases h with ⟨_, hbudget⟩
  unfold uniformRemainderCertificateSize
  omega

def sampleUniformRemainderCertificate : UniformRemainderCertificate where
  firstWindow := 3
  secondWindow := 4
  combinedWindow := 10
  scaleWindow := 2
  slack := 0

example :
    uniformRemainderCertificateReady sampleUniformRemainderCertificate := by
  norm_num [uniformRemainderCertificateReady,
    uniformRemainderCertificateControlled, sampleUniformRemainderCertificate]

example :
    sampleUniformRemainderCertificate.combinedWindow ≤
      uniformRemainderCertificateSize sampleUniformRemainderCertificate := by
  apply uniformRemainderCertificate_combined_le_size
  norm_num [uniformRemainderCertificateReady,
    uniformRemainderCertificateControlled, sampleUniformRemainderCertificate]

/-- A refinement certificate with a separate uniform-remainder budget. -/
structure UniformRemainderRefinementCertificate where
  firstWindow : ℕ
  secondWindow : ℕ
  combinedWindow : ℕ
  scaleWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ

def UniformRemainderRefinementCertificate.remainderControlled
    (cert : UniformRemainderRefinementCertificate) : Prop :=
  cert.firstWindow + cert.secondWindow ≤ cert.combinedWindow + cert.slack

def UniformRemainderRefinementCertificate.budgetControlled
    (cert : UniformRemainderRefinementCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.firstWindow + cert.secondWindow + cert.combinedWindow +
      cert.scaleWindow + cert.slack

def uniformRemainderRefinementReady
    (cert : UniformRemainderRefinementCertificate) : Prop :=
  cert.remainderControlled ∧ cert.budgetControlled

def UniformRemainderRefinementCertificate.size
    (cert : UniformRemainderRefinementCertificate) : ℕ :=
  cert.firstWindow + cert.secondWindow + cert.combinedWindow +
    cert.scaleWindow + cert.slack

theorem uniformRemainder_certificateBudgetWindow_le_size
    (cert : UniformRemainderRefinementCertificate)
    (h : uniformRemainderRefinementReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformRemainderRefinementCertificate :
    UniformRemainderRefinementCertificate where
  firstWindow := 3
  secondWindow := 4
  combinedWindow := 10
  scaleWindow := 2
  certificateBudgetWindow := 19
  slack := 0

example :
    uniformRemainderRefinementReady sampleUniformRemainderRefinementCertificate := by
  norm_num [uniformRemainderRefinementReady,
    UniformRemainderRefinementCertificate.remainderControlled,
    UniformRemainderRefinementCertificate.budgetControlled,
    sampleUniformRemainderRefinementCertificate]

example :
    sampleUniformRemainderRefinementCertificate.certificateBudgetWindow ≤
      sampleUniformRemainderRefinementCertificate.size := by
  apply uniformRemainder_certificateBudgetWindow_le_size
  norm_num [uniformRemainderRefinementReady,
    UniformRemainderRefinementCertificate.remainderControlled,
    UniformRemainderRefinementCertificate.budgetControlled,
    sampleUniformRemainderRefinementCertificate]


structure UniformRemainderAlgebraBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformRemainderAlgebraBudgetCertificate.controlled
    (c : UniformRemainderAlgebraBudgetCertificate) : Prop :=
  0 < c.primaryWindow ∧ c.secondaryWindow ≤ c.primaryWindow + c.slack

def UniformRemainderAlgebraBudgetCertificate.budgetControlled
    (c : UniformRemainderAlgebraBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def UniformRemainderAlgebraBudgetCertificate.Ready
    (c : UniformRemainderAlgebraBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UniformRemainderAlgebraBudgetCertificate.size
    (c : UniformRemainderAlgebraBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem uniformRemainderAlgebra_budgetCertificate_le_size
    (c : UniformRemainderAlgebraBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformRemainderAlgebraBudgetCertificate :
    UniformRemainderAlgebraBudgetCertificate :=
  { primaryWindow := 5
    secondaryWindow := 6
    certificateBudgetWindow := 12
    slack := 1 }

example : sampleUniformRemainderAlgebraBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformRemainderAlgebraBudgetCertificate.controlled,
      sampleUniformRemainderAlgebraBudgetCertificate]
  · norm_num [UniformRemainderAlgebraBudgetCertificate.budgetControlled,
      sampleUniformRemainderAlgebraBudgetCertificate]

example :
    sampleUniformRemainderAlgebraBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformRemainderAlgebraBudgetCertificate.size := by
  apply uniformRemainderAlgebra_budgetCertificate_le_size
  constructor
  · norm_num [UniformRemainderAlgebraBudgetCertificate.controlled,
      sampleUniformRemainderAlgebraBudgetCertificate]
  · norm_num [UniformRemainderAlgebraBudgetCertificate.budgetControlled,
      sampleUniformRemainderAlgebraBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleUniformRemainderAlgebraBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformRemainderAlgebraBudgetCertificate.controlled,
      sampleUniformRemainderAlgebraBudgetCertificate]
  · norm_num [UniformRemainderAlgebraBudgetCertificate.budgetControlled,
      sampleUniformRemainderAlgebraBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformRemainderAlgebraBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformRemainderAlgebraBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List UniformRemainderAlgebraBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformRemainderAlgebraBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleUniformRemainderAlgebraBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.UniformRemainderAlgebra
