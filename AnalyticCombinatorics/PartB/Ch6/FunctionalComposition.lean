import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Functional composition.

Finite composition-depth bookkeeping for transfer of singular expansions
through composed generating functions.
-/

namespace AnalyticCombinatorics.PartB.Ch6.FunctionalComposition

/-- Finite functional composition of natural coefficient proxies. -/
def composeProxy (outer inner : ℕ → ℕ) (n : ℕ) : ℕ :=
  outer (inner n)

/-- Finite composition envelope under a monotone outer envelope. -/
def compositionEnvelopeCheck
    (outer inner envelope : ℕ → ℕ) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => composeProxy outer inner n ≤ envelope n

def squareProxy (n : ℕ) : ℕ :=
  n ^ 2

def shiftProxy (n : ℕ) : ℕ :=
  n + 1

theorem squareShift_compositionEnvelope :
    compositionEnvelopeCheck squareProxy shiftProxy (fun n => (n + 1) ^ 2) 24 = true := by
  unfold compositionEnvelopeCheck composeProxy squareProxy shiftProxy
  native_decide

/-- Prefix sum of a composed coefficient model. -/
def compositionPrefix (outer inner : ℕ → ℕ) (N : ℕ) : ℕ :=
  (List.range (N + 1)).foldl
    (fun total n => total + composeProxy outer inner n) 0

theorem squareShift_compositionPrefixWindow :
    compositionPrefix squareProxy shiftProxy 3 = 30 := by
  unfold compositionPrefix composeProxy squareProxy shiftProxy
  native_decide

structure FunctionalCompositionWindow where
  outerExpansionDepth : ℕ
  innerExpansionDepth : ℕ
  compositionDepth : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def functionalCompositionReady (w : FunctionalCompositionWindow) : Prop :=
  0 < w.outerExpansionDepth ∧
    w.compositionDepth ≤
      w.outerExpansionDepth + w.innerExpansionDepth + w.slack

def functionalCompositionBudget (w : FunctionalCompositionWindow) : ℕ :=
  w.outerExpansionDepth + w.innerExpansionDepth + w.compositionDepth + w.slack

theorem compositionDepth_le_functionalCompositionBudget
    (w : FunctionalCompositionWindow) :
    w.compositionDepth ≤ functionalCompositionBudget w := by
  unfold functionalCompositionBudget
  omega

def sampleFunctionalCompositionWindow : FunctionalCompositionWindow :=
  { outerExpansionDepth := 4
    innerExpansionDepth := 5
    compositionDepth := 8
    slack := 1 }

example : functionalCompositionReady sampleFunctionalCompositionWindow := by
  norm_num [functionalCompositionReady, sampleFunctionalCompositionWindow]

structure FunctionalCompositionBudgetCertificate where
  outerWindow : ℕ
  innerWindow : ℕ
  compositionWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FunctionalCompositionBudgetCertificate.controlled
    (c : FunctionalCompositionBudgetCertificate) : Prop :=
  0 < c.outerWindow ∧
    c.compositionWindow ≤ c.outerWindow + c.innerWindow + c.slack

def FunctionalCompositionBudgetCertificate.budgetControlled
    (c : FunctionalCompositionBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.outerWindow + c.innerWindow + c.compositionWindow + c.slack

def FunctionalCompositionBudgetCertificate.Ready
    (c : FunctionalCompositionBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FunctionalCompositionBudgetCertificate.size
    (c : FunctionalCompositionBudgetCertificate) : ℕ :=
  c.outerWindow + c.innerWindow + c.compositionWindow + c.slack

theorem functionalComposition_budgetCertificate_le_size
    (c : FunctionalCompositionBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleFunctionalCompositionBudgetCertificate :
    FunctionalCompositionBudgetCertificate :=
  { outerWindow := 4
    innerWindow := 5
    compositionWindow := 8
    certificateBudgetWindow := 18
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFunctionalCompositionBudgetCertificate.Ready := by
  constructor
  · norm_num [FunctionalCompositionBudgetCertificate.controlled,
      sampleFunctionalCompositionBudgetCertificate]
  · norm_num [FunctionalCompositionBudgetCertificate.budgetControlled,
      sampleFunctionalCompositionBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFunctionalCompositionBudgetCertificate.certificateBudgetWindow ≤
      sampleFunctionalCompositionBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFunctionalCompositionBudgetCertificate.Ready := by
  constructor
  · norm_num [FunctionalCompositionBudgetCertificate.controlled,
      sampleFunctionalCompositionBudgetCertificate]
  · norm_num [FunctionalCompositionBudgetCertificate.budgetControlled,
      sampleFunctionalCompositionBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List FunctionalCompositionBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFunctionalCompositionBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleFunctionalCompositionBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch6.FunctionalComposition
