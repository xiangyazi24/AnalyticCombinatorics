import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Appendix C: probability spaces.

Finite sample-space and mass-budget bookkeeping.
-/

namespace AnalyticCombinatorics.AppC.ProbabilitySpaces

/-- Finite rational mass on an atom set. -/
def uniformMassQ (atomCount _ : ℕ) : ℚ :=
  1 / (atomCount : ℚ)

/-- Prefix mass over the first `N + 1` atoms. -/
def massPrefixQ (mass : ℕ → ℚ) (N : ℕ) : ℚ :=
  (List.range (N + 1)).foldl (fun total k => total + mass k) 0

/-- Finite nonnegative-mass audit. -/
def nonnegativeMassUpTo (mass : ℕ → ℚ) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun k => 0 ≤ mass k

/-- Finite probability-space statement with exact sampled normalization. -/
def FiniteProbabilitySpace (mass : ℕ → ℚ) (N : ℕ) : Prop :=
  nonnegativeMassUpTo mass N = true ∧ massPrefixQ mass N = 1

theorem uniformMass_probabilitySpace :
    FiniteProbabilitySpace (uniformMassQ 6) 5 := by
  unfold FiniteProbabilitySpace nonnegativeMassUpTo massPrefixQ uniformMassQ
  native_decide

/-- First moment over a finite probability prefix. -/
def massFirstMomentQ (mass : ℕ → ℚ) (N : ℕ) : ℚ :=
  (List.range (N + 1)).foldl
    (fun (total : ℚ) (k : ℕ) => total + k * mass k) 0

theorem uniformMass_firstMomentWindow :
    massFirstMomentQ (uniformMassQ 4) 3 = 3 / 2 := by
  unfold massFirstMomentQ uniformMassQ
  native_decide

structure FiniteProbabilitySpaceWindow where
  atomCount : ℕ
  totalMass : ℕ
  normalizationSlack : ℕ
deriving DecidableEq, Repr

def probabilitySpaceReady (w : FiniteProbabilitySpaceWindow) : Prop :=
  0 < w.atomCount ∧ w.totalMass ≤ w.atomCount + w.normalizationSlack

def probabilitySpaceBudget (w : FiniteProbabilitySpaceWindow) : ℕ :=
  w.atomCount + w.totalMass + w.normalizationSlack

theorem totalMass_le_budget (w : FiniteProbabilitySpaceWindow) :
    w.totalMass ≤ probabilitySpaceBudget w := by
  unfold probabilitySpaceBudget
  omega

def sampleProbabilitySpaceWindow : FiniteProbabilitySpaceWindow :=
  { atomCount := 6, totalMass := 6, normalizationSlack := 0 }

example : probabilitySpaceReady sampleProbabilitySpaceWindow := by
  norm_num [probabilitySpaceReady, sampleProbabilitySpaceWindow]

structure ProbabilitySpacesBudgetCertificate where
  atomWindow : ℕ
  massWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ProbabilitySpacesBudgetCertificate.controlled
    (c : ProbabilitySpacesBudgetCertificate) : Prop :=
  0 < c.atomWindow ∧ c.massWindow ≤ c.atomWindow + c.slack

def ProbabilitySpacesBudgetCertificate.budgetControlled
    (c : ProbabilitySpacesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.atomWindow + c.massWindow + c.slack

def ProbabilitySpacesBudgetCertificate.Ready
    (c : ProbabilitySpacesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ProbabilitySpacesBudgetCertificate.size
    (c : ProbabilitySpacesBudgetCertificate) : ℕ :=
  c.atomWindow + c.massWindow + c.slack

theorem probabilitySpaces_budgetCertificate_le_size
    (c : ProbabilitySpacesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleProbabilitySpacesBudgetCertificate :
    ProbabilitySpacesBudgetCertificate :=
  { atomWindow := 6
    massWindow := 6
    certificateBudgetWindow := 13
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleProbabilitySpacesBudgetCertificate.Ready := by
  constructor
  · norm_num [ProbabilitySpacesBudgetCertificate.controlled,
      sampleProbabilitySpacesBudgetCertificate]
  · norm_num [ProbabilitySpacesBudgetCertificate.budgetControlled,
      sampleProbabilitySpacesBudgetCertificate]

example : sampleProbabilitySpacesBudgetCertificate.Ready := by
  constructor
  · norm_num [ProbabilitySpacesBudgetCertificate.controlled,
      sampleProbabilitySpacesBudgetCertificate]
  · norm_num [ProbabilitySpacesBudgetCertificate.budgetControlled,
      sampleProbabilitySpacesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleProbabilitySpacesBudgetCertificate.certificateBudgetWindow ≤
      sampleProbabilitySpacesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List ProbabilitySpacesBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleProbabilitySpacesBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleProbabilitySpacesBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.ProbabilitySpaces
