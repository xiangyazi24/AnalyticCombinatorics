import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.Basic

structure FiniteClassWindow where
  atomCount : ℕ
  constructionDepth : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def nonemptyAtoms (w : FiniteClassWindow) : Prop :=
  0 < w.atomCount

def constructionDepthControlled (w : FiniteClassWindow) : Prop :=
  w.constructionDepth ≤ w.atomCount + w.slack

def finiteClassWindowReady (w : FiniteClassWindow) : Prop :=
  nonemptyAtoms w ∧ constructionDepthControlled w

def finiteClassWindowBudget (w : FiniteClassWindow) : ℕ :=
  w.atomCount + w.constructionDepth + w.slack

theorem finiteClassWindowReady.certificate {w : FiniteClassWindow}
    (h : finiteClassWindowReady w) :
    nonemptyAtoms w ∧ constructionDepthControlled w ∧
      w.constructionDepth ≤ finiteClassWindowBudget w := by
  rcases h with ⟨hatoms, hdepth⟩
  refine ⟨hatoms, hdepth, ?_⟩
  unfold finiteClassWindowBudget
  omega

theorem atomCount_le_budget (w : FiniteClassWindow) :
    w.atomCount ≤ finiteClassWindowBudget w := by
  unfold finiteClassWindowBudget
  omega

def sampleFiniteClassWindow : FiniteClassWindow :=
  { atomCount := 4, constructionDepth := 5, slack := 1 }

example : finiteClassWindowReady sampleFiniteClassWindow := by
  norm_num [finiteClassWindowReady, nonemptyAtoms,
    constructionDepthControlled, sampleFiniteClassWindow]

example : finiteClassWindowBudget sampleFiniteClassWindow = 10 := by
  native_decide

structure ConstructionProfile where
  atoms : ℕ
  operators : ℕ
  equations : ℕ
  proofBudget : ℕ
deriving DecidableEq, Repr

def ConstructionProfile.ready (p : ConstructionProfile) : Prop :=
  0 < p.atoms ∧ p.operators ≤ p.proofBudget ∧ p.equations ≤ p.proofBudget

def ConstructionProfile.certificate (p : ConstructionProfile) : ℕ :=
  p.atoms + p.operators + p.equations + p.proofBudget

theorem operators_le_certificate (p : ConstructionProfile) :
    p.operators ≤ p.certificate := by
  unfold ConstructionProfile.certificate
  omega

def sampleConstructionProfile : ConstructionProfile :=
  { atoms := 4, operators := 3, equations := 2, proofBudget := 5 }

example : sampleConstructionProfile.ready := by
  norm_num [sampleConstructionProfile, ConstructionProfile.ready]

structure BasicBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BasicBudgetCertificate.controlled (c : BasicBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def BasicBudgetCertificate.budgetControlled
    (c : BasicBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def BasicBudgetCertificate.Ready (c : BasicBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BasicBudgetCertificate.size (c : BasicBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem basic_budgetCertificate_le_size
    (c : BasicBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleBasicBudgetCertificate : BasicBudgetCertificate :=
  { primaryWindow := 4
    secondaryWindow := 5
    certificateBudgetWindow := 10
    slack := 1 }

example : sampleBasicBudgetCertificate.Ready := by
  constructor
  · norm_num [BasicBudgetCertificate.controlled, sampleBasicBudgetCertificate]
  · norm_num [BasicBudgetCertificate.budgetControlled,
      sampleBasicBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleBasicBudgetCertificate.Ready := by
  constructor
  · norm_num [BasicBudgetCertificate.controlled,
      sampleBasicBudgetCertificate]
  · norm_num [BasicBudgetCertificate.budgetControlled,
      sampleBasicBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleBasicBudgetCertificate.certificateBudgetWindow ≤
      sampleBasicBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List BasicBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleBasicBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleBasicBudgetCertificate
  native_decide

end AnalyticCombinatorics.Basic
