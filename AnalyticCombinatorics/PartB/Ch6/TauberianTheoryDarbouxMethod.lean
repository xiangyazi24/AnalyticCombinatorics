import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Tauberian theory and Darboux's method.

Finite boundary-window bookkeeping for Tauberian and Darboux transfer
certificates.
-/

namespace AnalyticCombinatorics.PartB.Ch6.TauberianTheoryDarbouxMethod

/-- Finite Darboux boundary coefficient model. -/
def darbouxBoundaryCoeff (order n : ℕ) : ℕ :=
  (n + 1) ^ order

/-- Partial sums used for Tauberian comparison. -/
def tauberianPartialSum (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  (List.range (n + 1)).foldl (fun total k => total + a k) 0

/-- Finite comparison between coefficient and summatory forms. -/
def tauberianDarbouxComparisonCheck (order N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    darbouxBoundaryCoeff order n ≤ tauberianPartialSum (darbouxBoundaryCoeff order) n

theorem tauberianDarbouxComparison_window :
    tauberianDarbouxComparisonCheck 2 20 = true := by
  unfold tauberianDarbouxComparisonCheck tauberianPartialSum
    darbouxBoundaryCoeff
  native_decide

structure TauberianDarbouxWindow where
  boundaryWindow : ℕ
  coefficientWindow : ℕ
  remainderWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def tauberianDarbouxReady (w : TauberianDarbouxWindow) : Prop :=
  0 < w.boundaryWindow ∧
    w.coefficientWindow ≤ w.boundaryWindow + w.remainderWindow + w.slack

def tauberianDarbouxBudget (w : TauberianDarbouxWindow) : ℕ :=
  w.boundaryWindow + w.coefficientWindow + w.remainderWindow + w.slack

theorem coefficientWindow_le_tauberianDarbouxBudget
    (w : TauberianDarbouxWindow) :
    w.coefficientWindow ≤ tauberianDarbouxBudget w := by
  unfold tauberianDarbouxBudget
  omega

def sampleTauberianDarbouxWindow : TauberianDarbouxWindow :=
  { boundaryWindow := 5, coefficientWindow := 7, remainderWindow := 3, slack := 1 }

example : tauberianDarbouxReady sampleTauberianDarbouxWindow := by
  norm_num [tauberianDarbouxReady, sampleTauberianDarbouxWindow]

structure TauberianTheoryDarbouxMethodBudgetCertificate where
  boundaryWindow : ℕ
  coefficientWindow : ℕ
  remainderWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TauberianTheoryDarbouxMethodBudgetCertificate.controlled
    (c : TauberianTheoryDarbouxMethodBudgetCertificate) : Prop :=
  0 < c.boundaryWindow ∧
    c.coefficientWindow ≤ c.boundaryWindow + c.remainderWindow + c.slack

def TauberianTheoryDarbouxMethodBudgetCertificate.budgetControlled
    (c : TauberianTheoryDarbouxMethodBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.boundaryWindow + c.coefficientWindow + c.remainderWindow + c.slack

def TauberianTheoryDarbouxMethodBudgetCertificate.Ready
    (c : TauberianTheoryDarbouxMethodBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def TauberianTheoryDarbouxMethodBudgetCertificate.size
    (c : TauberianTheoryDarbouxMethodBudgetCertificate) : ℕ :=
  c.boundaryWindow + c.coefficientWindow + c.remainderWindow + c.slack

theorem tauberianTheoryDarbouxMethod_budgetCertificate_le_size
    (c : TauberianTheoryDarbouxMethodBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleTauberianTheoryDarbouxMethodBudgetCertificate :
    TauberianTheoryDarbouxMethodBudgetCertificate :=
  { boundaryWindow := 5
    coefficientWindow := 7
    remainderWindow := 3
    certificateBudgetWindow := 16
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleTauberianTheoryDarbouxMethodBudgetCertificate.Ready := by
  constructor
  · norm_num [TauberianTheoryDarbouxMethodBudgetCertificate.controlled,
      sampleTauberianTheoryDarbouxMethodBudgetCertificate]
  · norm_num [TauberianTheoryDarbouxMethodBudgetCertificate.budgetControlled,
      sampleTauberianTheoryDarbouxMethodBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleTauberianTheoryDarbouxMethodBudgetCertificate.certificateBudgetWindow ≤
      sampleTauberianTheoryDarbouxMethodBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleTauberianTheoryDarbouxMethodBudgetCertificate.Ready := by
  constructor
  · norm_num [TauberianTheoryDarbouxMethodBudgetCertificate.controlled,
      sampleTauberianTheoryDarbouxMethodBudgetCertificate]
  · norm_num [TauberianTheoryDarbouxMethodBudgetCertificate.budgetControlled,
      sampleTauberianTheoryDarbouxMethodBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List TauberianTheoryDarbouxMethodBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleTauberianTheoryDarbouxMethodBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleTauberianTheoryDarbouxMethodBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch6.TauberianTheoryDarbouxMethod
