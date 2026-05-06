import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite Hadamard product models.

The finite record stores left support, right support, and diagonal slack
for coefficientwise products.
-/

namespace AnalyticCombinatorics.AppA.FiniteHadamardProductModels

structure HadamardProductData where
  leftSupport : ℕ
  rightSupport : ℕ
  diagonalSlack : ℕ
deriving DecidableEq, Repr

def leftSupportPositive (d : HadamardProductData) : Prop :=
  0 < d.leftSupport

def rightSupportControlled (d : HadamardProductData) : Prop :=
  d.rightSupport ≤ d.leftSupport + d.diagonalSlack

def hadamardProductReady (d : HadamardProductData) : Prop :=
  leftSupportPositive d ∧ rightSupportControlled d

def hadamardProductBudget (d : HadamardProductData) : ℕ :=
  d.leftSupport + d.rightSupport + d.diagonalSlack

theorem hadamardProductReady.left {d : HadamardProductData}
    (h : hadamardProductReady d) :
    leftSupportPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem rightSupport_le_hadamardBudget (d : HadamardProductData) :
    d.rightSupport ≤ hadamardProductBudget d := by
  unfold hadamardProductBudget
  omega

def sampleHadamardProductData : HadamardProductData :=
  { leftSupport := 6, rightSupport := 8, diagonalSlack := 3 }

example : hadamardProductReady sampleHadamardProductData := by
  norm_num [hadamardProductReady, leftSupportPositive]
  norm_num [rightSupportControlled, sampleHadamardProductData]

example : hadamardProductBudget sampleHadamardProductData = 17 := by
  native_decide

structure HadamardProductWindow where
  leftSupport : ℕ
  rightSupport : ℕ
  diagonalSlack : ℕ
  diagonalBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def HadamardProductWindow.rightSupportControlled (w : HadamardProductWindow) : Prop :=
  w.rightSupport ≤ w.leftSupport + w.diagonalSlack + w.slack

def HadamardProductWindow.diagonalControlled (w : HadamardProductWindow) : Prop :=
  w.diagonalBudget ≤ w.leftSupport + w.rightSupport + w.diagonalSlack + w.slack

def hadamardProductWindowReady (w : HadamardProductWindow) : Prop :=
  0 < w.leftSupport ∧
    w.rightSupportControlled ∧
    w.diagonalControlled

def HadamardProductWindow.certificate (w : HadamardProductWindow) : ℕ :=
  w.leftSupport + w.rightSupport + w.diagonalSlack + w.slack

theorem hadamardProduct_diagonalBudget_le_certificate {w : HadamardProductWindow}
    (h : hadamardProductWindowReady w) :
    w.diagonalBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hdiag⟩
  exact hdiag

def sampleHadamardProductWindow : HadamardProductWindow :=
  { leftSupport := 6, rightSupport := 8, diagonalSlack := 3, diagonalBudget := 16, slack := 0 }

example : hadamardProductWindowReady sampleHadamardProductWindow := by
  norm_num [hadamardProductWindowReady, HadamardProductWindow.rightSupportControlled,
    HadamardProductWindow.diagonalControlled, sampleHadamardProductWindow]

example : sampleHadamardProductWindow.certificate = 17 := by
  native_decide


structure FiniteHadamardProductModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteHadamardProductModelsBudgetCertificate.controlled
    (c : FiniteHadamardProductModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteHadamardProductModelsBudgetCertificate.budgetControlled
    (c : FiniteHadamardProductModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteHadamardProductModelsBudgetCertificate.Ready
    (c : FiniteHadamardProductModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteHadamardProductModelsBudgetCertificate.size
    (c : FiniteHadamardProductModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteHadamardProductModels_budgetCertificate_le_size
    (c : FiniteHadamardProductModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteHadamardProductModelsBudgetCertificate :
    FiniteHadamardProductModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteHadamardProductModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteHadamardProductModelsBudgetCertificate.controlled,
      sampleFiniteHadamardProductModelsBudgetCertificate]
  · norm_num [FiniteHadamardProductModelsBudgetCertificate.budgetControlled,
      sampleFiniteHadamardProductModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteHadamardProductModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteHadamardProductModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteHadamardProductModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteHadamardProductModelsBudgetCertificate.controlled,
      sampleFiniteHadamardProductModelsBudgetCertificate]
  · norm_num [FiniteHadamardProductModelsBudgetCertificate.budgetControlled,
      sampleFiniteHadamardProductModelsBudgetCertificate]

example :
    sampleFiniteHadamardProductModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteHadamardProductModelsBudgetCertificate.size := by
  apply finiteHadamardProductModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteHadamardProductModelsBudgetCertificate.controlled,
      sampleFiniteHadamardProductModelsBudgetCertificate]
  · norm_num [FiniteHadamardProductModelsBudgetCertificate.budgetControlled,
      sampleFiniteHadamardProductModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List FiniteHadamardProductModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteHadamardProductModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteHadamardProductModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteHadamardProductModels
