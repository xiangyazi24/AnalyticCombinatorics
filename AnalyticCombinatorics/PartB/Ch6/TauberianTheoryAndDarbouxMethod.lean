import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Tauberian theory and Darboux's method
-/

namespace AnalyticCombinatorics.PartB.Ch6.TauberianTheoryAndDarbouxMethod

/-- Finite comparison datum linking monotone Tauberian bounds and Darboux truncation. -/
structure TauberianDarbouxComparison where
  tauberianBound : ℕ
  darbouxBound : ℕ
  comparisonSlack : ℕ
deriving DecidableEq, Repr

def TauberianDarbouxComparison.compatible
    (c : TauberianDarbouxComparison) : Prop :=
  c.tauberianBound ≤ c.darbouxBound + c.comparisonSlack

theorem tauberianDarbouxComparison_sample :
    ({ tauberianBound := 10, darbouxBound := 7,
       comparisonSlack := 3 } : TauberianDarbouxComparison).compatible := by
  norm_num [TauberianDarbouxComparison.compatible]

/-- Cleared Darboux truncation envelope. -/
def darbouxTruncationEnvelope (truncation remainder : ℕ) : ℕ :=
  truncation + remainder

theorem darbouxTruncationEnvelope_sample :
    darbouxTruncationEnvelope 7 3 = 10 := by
  native_decide

structure TauberianDarbouxWindow where
  tauberianWindow : ℕ
  darbouxWindow : ℕ
  comparisonWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TauberianDarbouxWindow.ready (w : TauberianDarbouxWindow) : Prop :=
  0 < w.tauberianWindow ∧
    w.comparisonWindow ≤ w.tauberianWindow + w.darbouxWindow + w.slack

def sampleTauberianDarbouxWindow : TauberianDarbouxWindow :=
  { tauberianWindow := 4
    darbouxWindow := 5
    comparisonWindow := 10
    slack := 1 }

example : sampleTauberianDarbouxWindow.ready := by
  norm_num [TauberianDarbouxWindow.ready, sampleTauberianDarbouxWindow]

structure TauberianTheoryAndDarbouxMethodBudgetCertificate where
  tauberianWindow : ℕ
  darbouxWindow : ℕ
  comparisonWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TauberianTheoryAndDarbouxMethodBudgetCertificate.controlled
    (c : TauberianTheoryAndDarbouxMethodBudgetCertificate) : Prop :=
  0 < c.tauberianWindow ∧
    c.comparisonWindow ≤ c.tauberianWindow + c.darbouxWindow + c.slack

def TauberianTheoryAndDarbouxMethodBudgetCertificate.budgetControlled
    (c : TauberianTheoryAndDarbouxMethodBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.tauberianWindow + c.darbouxWindow + c.comparisonWindow + c.slack

def TauberianTheoryAndDarbouxMethodBudgetCertificate.Ready
    (c : TauberianTheoryAndDarbouxMethodBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def TauberianTheoryAndDarbouxMethodBudgetCertificate.size
    (c : TauberianTheoryAndDarbouxMethodBudgetCertificate) : ℕ :=
  c.tauberianWindow + c.darbouxWindow + c.comparisonWindow + c.slack

def sampleTauberianTheoryAndDarbouxMethodBudgetCertificate :
    TauberianTheoryAndDarbouxMethodBudgetCertificate :=
  { tauberianWindow := 4
    darbouxWindow := 5
    comparisonWindow := 10
    certificateBudgetWindow := 20
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleTauberianTheoryAndDarbouxMethodBudgetCertificate.Ready := by
  constructor
  · norm_num [TauberianTheoryAndDarbouxMethodBudgetCertificate.controlled,
      sampleTauberianTheoryAndDarbouxMethodBudgetCertificate]
  · norm_num [TauberianTheoryAndDarbouxMethodBudgetCertificate.budgetControlled,
      sampleTauberianTheoryAndDarbouxMethodBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleTauberianTheoryAndDarbouxMethodBudgetCertificate.certificateBudgetWindow ≤
      sampleTauberianTheoryAndDarbouxMethodBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleTauberianTheoryAndDarbouxMethodBudgetCertificate.Ready := by
  constructor
  · norm_num [TauberianTheoryAndDarbouxMethodBudgetCertificate.controlled,
      sampleTauberianTheoryAndDarbouxMethodBudgetCertificate]
  · norm_num [TauberianTheoryAndDarbouxMethodBudgetCertificate.budgetControlled,
      sampleTauberianTheoryAndDarbouxMethodBudgetCertificate]

def budgetCertificateListReady
    (data : List TauberianTheoryAndDarbouxMethodBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem sampleTauberianTheoryAndDarbouxMethodBudgetCertificate_ready :
    sampleTauberianTheoryAndDarbouxMethodBudgetCertificate.Ready := by
  constructor
  · norm_num [TauberianTheoryAndDarbouxMethodBudgetCertificate.controlled,
      sampleTauberianTheoryAndDarbouxMethodBudgetCertificate]
  · norm_num [TauberianTheoryAndDarbouxMethodBudgetCertificate.budgetControlled,
      sampleTauberianTheoryAndDarbouxMethodBudgetCertificate]

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleTauberianTheoryAndDarbouxMethodBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleTauberianTheoryAndDarbouxMethodBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch6.TauberianTheoryAndDarbouxMethod
