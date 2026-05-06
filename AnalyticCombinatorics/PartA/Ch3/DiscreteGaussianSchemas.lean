import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Discrete Gaussian limit-law bookkeeping.

The file records integer mean/variance windows and lattice span checks for
local limit schemas.
-/

namespace AnalyticCombinatorics.PartA.Ch3.DiscreteGaussianSchemas

structure DiscreteGaussianData where
  meanNumerator : ℕ
  varianceNumerator : ℕ
  latticeSpan : ℕ
deriving DecidableEq, Repr

def nondegenerateVariance (d : DiscreteGaussianData) : Prop :=
  0 < d.varianceNumerator

def unitLatticeSpan (d : DiscreteGaussianData) : Prop :=
  d.latticeSpan = 1

def discreteGaussianReady (d : DiscreteGaussianData) : Prop :=
  nondegenerateVariance d ∧ unitLatticeSpan d

def centeredIndex (d : DiscreteGaussianData) (n : ℕ) : ℕ :=
  d.meanNumerator + n * d.latticeSpan

theorem discreteGaussianReady.variance {d : DiscreteGaussianData}
    (h : discreteGaussianReady d) :
    nondegenerateVariance d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem centeredIndex_succ (d : DiscreteGaussianData) (n : ℕ) :
    centeredIndex d (n + 1) = centeredIndex d n + d.latticeSpan := by
  unfold centeredIndex
  rw [Nat.succ_mul]
  omega

def sampleGaussian : DiscreteGaussianData :=
  { meanNumerator := 5, varianceNumerator := 8, latticeSpan := 1 }

example : discreteGaussianReady sampleGaussian := by
  norm_num [discreteGaussianReady, nondegenerateVariance, unitLatticeSpan, sampleGaussian]

example : centeredIndex sampleGaussian 4 = 9 := by
  native_decide

structure DiscreteGaussianWindow where
  meanNumerator : ℕ
  varianceNumerator : ℕ
  latticeSpan : ℕ
  localMassBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DiscreteGaussianWindow.massControlled (w : DiscreteGaussianWindow) : Prop :=
  w.localMassBudget ≤ w.meanNumerator + w.varianceNumerator + w.latticeSpan + w.slack

def discreteGaussianWindowReady (w : DiscreteGaussianWindow) : Prop :=
  0 < w.varianceNumerator ∧
    w.latticeSpan = 1 ∧
    w.massControlled

def DiscreteGaussianWindow.certificate (w : DiscreteGaussianWindow) : ℕ :=
  w.meanNumerator + w.varianceNumerator + w.latticeSpan + w.slack

theorem discreteGaussian_localMassBudget_le_certificate {w : DiscreteGaussianWindow}
    (h : discreteGaussianWindowReady w) :
    w.localMassBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hmass⟩
  exact hmass

def sampleDiscreteGaussianWindow : DiscreteGaussianWindow :=
  { meanNumerator := 5, varianceNumerator := 8, latticeSpan := 1, localMassBudget := 13,
    slack := 0 }

example : discreteGaussianWindowReady sampleDiscreteGaussianWindow := by
  norm_num [discreteGaussianWindowReady, DiscreteGaussianWindow.massControlled,
    sampleDiscreteGaussianWindow]

example : sampleDiscreteGaussianWindow.certificate = 14 := by
  native_decide


structure DiscreteGaussianSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DiscreteGaussianSchemasBudgetCertificate.controlled
    (c : DiscreteGaussianSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def DiscreteGaussianSchemasBudgetCertificate.budgetControlled
    (c : DiscreteGaussianSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def DiscreteGaussianSchemasBudgetCertificate.Ready
    (c : DiscreteGaussianSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def DiscreteGaussianSchemasBudgetCertificate.size
    (c : DiscreteGaussianSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem discreteGaussianSchemas_budgetCertificate_le_size
    (c : DiscreteGaussianSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleDiscreteGaussianSchemasBudgetCertificate :
    DiscreteGaussianSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleDiscreteGaussianSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [DiscreteGaussianSchemasBudgetCertificate.controlled,
      sampleDiscreteGaussianSchemasBudgetCertificate]
  · norm_num [DiscreteGaussianSchemasBudgetCertificate.budgetControlled,
      sampleDiscreteGaussianSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleDiscreteGaussianSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleDiscreteGaussianSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleDiscreteGaussianSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [DiscreteGaussianSchemasBudgetCertificate.controlled,
      sampleDiscreteGaussianSchemasBudgetCertificate]
  · norm_num [DiscreteGaussianSchemasBudgetCertificate.budgetControlled,
      sampleDiscreteGaussianSchemasBudgetCertificate]

example :
    sampleDiscreteGaussianSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleDiscreteGaussianSchemasBudgetCertificate.size := by
  apply discreteGaussianSchemas_budgetCertificate_le_size
  constructor
  · norm_num [DiscreteGaussianSchemasBudgetCertificate.controlled,
      sampleDiscreteGaussianSchemasBudgetCertificate]
  · norm_num [DiscreteGaussianSchemasBudgetCertificate.budgetControlled,
      sampleDiscreteGaussianSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List DiscreteGaussianSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleDiscreteGaussianSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleDiscreteGaussianSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch3.DiscreteGaussianSchemas
