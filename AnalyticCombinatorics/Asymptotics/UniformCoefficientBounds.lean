import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform coefficient-bound bookkeeping.

The module records finite pointwise coefficient budgets and prefix
majorants.
-/

namespace AnalyticCombinatorics.Asymptotics.UniformCoefficientBounds

def coefficientsBoundedBy (a : ℕ → ℕ) (bound : ℕ) (N : ℕ) : Prop :=
  ∀ n, n ≤ N → a n ≤ bound

def prefixCoefficientMass (a : ℕ → ℕ) (N : ℕ) : ℕ :=
  (List.range (N + 1)).map a |>.sum

def constantCoeff (c : ℕ) (n : ℕ) : ℕ := c + (n - n)

theorem coefficientsBoundedBy_mono {a : ℕ → ℕ} {b c N : ℕ}
    (h : coefficientsBoundedBy a b N) (hbc : b ≤ c) :
    coefficientsBoundedBy a c N := by
  intro n hn
  exact le_trans (h n hn) hbc

theorem prefixCoefficientMass_zero (a : ℕ → ℕ) :
    prefixCoefficientMass a 0 = a 0 := by
  simp [prefixCoefficientMass]

example : prefixCoefficientMass (constantCoeff 3) 4 = 15 := by
  native_decide

example : coefficientsBoundedBy (constantCoeff 3) 5 7 := by
  intro n hn
  norm_num [constantCoeff]

structure UniformCoefficientWindow where
  cutoff : ℕ
  pointwiseBound : ℕ
  prefixMassBound : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformCoefficientWindow.ready (w : UniformCoefficientWindow) : Prop :=
  w.prefixMassBound ≤ (w.cutoff + 1) * w.pointwiseBound + w.slack

def UniformCoefficientWindow.nonzeroWindow (w : UniformCoefficientWindow) : Prop :=
  0 < w.cutoff + 1

def UniformCoefficientWindow.certificate (w : UniformCoefficientWindow) : ℕ :=
  w.cutoff + w.pointwiseBound + w.prefixMassBound + w.slack

theorem pointwiseBound_le_certificate (w : UniformCoefficientWindow) :
    w.pointwiseBound ≤ w.certificate := by
  unfold UniformCoefficientWindow.certificate
  omega

def sampleUniformCoefficientWindow : UniformCoefficientWindow :=
  { cutoff := 4, pointwiseBound := 3, prefixMassBound := 15, slack := 0 }

example : sampleUniformCoefficientWindow.ready := by
  norm_num [sampleUniformCoefficientWindow, UniformCoefficientWindow.ready]

example : sampleUniformCoefficientWindow.nonzeroWindow := by
  norm_num [sampleUniformCoefficientWindow, UniformCoefficientWindow.nonzeroWindow]

/-- A refinement certificate for uniform coefficient windows. -/
structure UniformCoefficientCertificate where
  cutoffWindow : ℕ
  pointwiseWindow : ℕ
  prefixWindow : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- The prefix bound is controlled by cutoff and pointwise bounds. -/
def uniformCoefficientCertificateControlled
    (w : UniformCoefficientCertificate) : Prop :=
  w.prefixWindow ≤ (w.cutoffWindow + 1) * w.pointwiseWindow + w.slack

/-- Readiness for a uniform coefficient certificate. -/
def uniformCoefficientCertificateReady
    (w : UniformCoefficientCertificate) : Prop :=
  uniformCoefficientCertificateControlled w ∧
    w.certificateBudget ≤ w.cutoffWindow + w.prefixWindow + w.slack

/-- Total size of a uniform coefficient certificate. -/
def uniformCoefficientCertificateSize
    (w : UniformCoefficientCertificate) : ℕ :=
  w.cutoffWindow + w.pointwiseWindow + w.prefixWindow +
    w.certificateBudget + w.slack

theorem uniformCoefficientCertificate_budget_le_size
    (w : UniformCoefficientCertificate)
    (h : uniformCoefficientCertificateReady w) :
    w.certificateBudget ≤ uniformCoefficientCertificateSize w := by
  rcases h with ⟨_, hbudget⟩
  unfold uniformCoefficientCertificateSize
  omega

def sampleUniformCoefficientCertificate : UniformCoefficientCertificate where
  cutoffWindow := 4
  pointwiseWindow := 3
  prefixWindow := 15
  certificateBudget := 19
  slack := 0

example :
    uniformCoefficientCertificateReady
      sampleUniformCoefficientCertificate := by
  norm_num [uniformCoefficientCertificateReady,
    uniformCoefficientCertificateControlled, sampleUniformCoefficientCertificate]

example :
    sampleUniformCoefficientCertificate.certificateBudget ≤
      uniformCoefficientCertificateSize sampleUniformCoefficientCertificate := by
  apply uniformCoefficientCertificate_budget_le_size
  norm_num [uniformCoefficientCertificateReady,
    uniformCoefficientCertificateControlled, sampleUniformCoefficientCertificate]

structure UniformCoefficientRefinementCertificate where
  cutoffWindow : ℕ
  pointwiseWindow : ℕ
  prefixWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformCoefficientRefinementCertificate.prefixControlled
    (c : UniformCoefficientRefinementCertificate) : Prop :=
  c.prefixWindow ≤ (c.cutoffWindow + 1) * c.pointwiseWindow + c.slack

def UniformCoefficientRefinementCertificate.certificateBudgetControlled
    (c : UniformCoefficientRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.cutoffWindow + c.pointwiseWindow + c.prefixWindow + c.slack

def uniformCoefficientRefinementReady
    (c : UniformCoefficientRefinementCertificate) : Prop :=
  c.prefixControlled ∧ c.certificateBudgetControlled

def UniformCoefficientRefinementCertificate.size
    (c : UniformCoefficientRefinementCertificate) : ℕ :=
  c.cutoffWindow + c.pointwiseWindow + c.prefixWindow + c.slack

theorem uniformCoefficient_certificateBudgetWindow_le_size
    {c : UniformCoefficientRefinementCertificate}
    (h : uniformCoefficientRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformCoefficientRefinementCertificate :
    UniformCoefficientRefinementCertificate :=
  { cutoffWindow := 4, pointwiseWindow := 3, prefixWindow := 15,
    certificateBudgetWindow := 22, slack := 0 }

example : uniformCoefficientRefinementReady
    sampleUniformCoefficientRefinementCertificate := by
  norm_num [uniformCoefficientRefinementReady,
    UniformCoefficientRefinementCertificate.prefixControlled,
    UniformCoefficientRefinementCertificate.certificateBudgetControlled,
    sampleUniformCoefficientRefinementCertificate]

example :
    sampleUniformCoefficientRefinementCertificate.certificateBudgetWindow ≤
      sampleUniformCoefficientRefinementCertificate.size := by
  norm_num [UniformCoefficientRefinementCertificate.size,
    sampleUniformCoefficientRefinementCertificate]

structure UniformCoefficientBudgetCertificate where
  cutoffWindow : ℕ
  pointwiseWindow : ℕ
  prefixWindow : ℕ
  prefixBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformCoefficientBudgetCertificate.controlled
    (c : UniformCoefficientBudgetCertificate) : Prop :=
  c.prefixWindow ≤ (c.cutoffWindow + 1) * c.pointwiseWindow + c.slack ∧
    c.prefixBudgetWindow ≤
      c.cutoffWindow + c.pointwiseWindow + c.prefixWindow + c.slack

def UniformCoefficientBudgetCertificate.budgetControlled
    (c : UniformCoefficientBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.cutoffWindow + c.pointwiseWindow + c.prefixWindow +
      c.prefixBudgetWindow + c.slack

def UniformCoefficientBudgetCertificate.Ready
    (c : UniformCoefficientBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UniformCoefficientBudgetCertificate.size
    (c : UniformCoefficientBudgetCertificate) : ℕ :=
  c.cutoffWindow + c.pointwiseWindow + c.prefixWindow +
    c.prefixBudgetWindow + c.slack

theorem uniformCoefficient_budgetCertificate_le_size
    (c : UniformCoefficientBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformCoefficientBudgetCertificate :
    UniformCoefficientBudgetCertificate :=
  { cutoffWindow := 4
    pointwiseWindow := 3
    prefixWindow := 15
    prefixBudgetWindow := 22
    certificateBudgetWindow := 44
    slack := 0 }

example : sampleUniformCoefficientBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformCoefficientBudgetCertificate.controlled,
      sampleUniformCoefficientBudgetCertificate]
  · norm_num [UniformCoefficientBudgetCertificate.budgetControlled,
      sampleUniformCoefficientBudgetCertificate]

example :
    sampleUniformCoefficientBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformCoefficientBudgetCertificate.size := by
  apply uniformCoefficient_budgetCertificate_le_size
  constructor
  · norm_num [UniformCoefficientBudgetCertificate.controlled,
      sampleUniformCoefficientBudgetCertificate]
  · norm_num [UniformCoefficientBudgetCertificate.budgetControlled,
      sampleUniformCoefficientBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleUniformCoefficientBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformCoefficientBudgetCertificate.controlled,
      sampleUniformCoefficientBudgetCertificate]
  · norm_num [UniformCoefficientBudgetCertificate.budgetControlled,
      sampleUniformCoefficientBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformCoefficientBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformCoefficientBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List UniformCoefficientBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformCoefficientBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleUniformCoefficientBudgetCertificate
  native_decide

end AnalyticCombinatorics.Asymptotics.UniformCoefficientBounds
