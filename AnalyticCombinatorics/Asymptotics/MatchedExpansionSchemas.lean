import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Matched-expansion schema bookkeeping.

The file records inner/outer expansion orders and matching error budgets.
-/

namespace AnalyticCombinatorics.Asymptotics.MatchedExpansionSchemas

structure MatchedExpansionData where
  innerOrder : ℕ
  outerOrder : ℕ
  matchingError : ℕ
deriving DecidableEq, Repr

def positiveOrders (d : MatchedExpansionData) : Prop :=
  0 < d.innerOrder ∧ 0 < d.outerOrder

def matchingErrorControlled (d : MatchedExpansionData) : Prop :=
  d.matchingError ≤ d.innerOrder + d.outerOrder

def matchedExpansionReady (d : MatchedExpansionData) : Prop :=
  positiveOrders d ∧ matchingErrorControlled d

def matchedOrderBudget (d : MatchedExpansionData) : ℕ :=
  d.innerOrder + d.outerOrder + d.matchingError

theorem matchedExpansionReady.orders {d : MatchedExpansionData}
    (h : matchedExpansionReady d) :
    positiveOrders d ∧ matchingErrorControlled d ∧ d.matchingError ≤ matchedOrderBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold matchedOrderBudget
  omega

theorem innerOrder_le_budget (d : MatchedExpansionData) :
    d.innerOrder ≤ matchedOrderBudget d := by
  unfold matchedOrderBudget
  omega

def sampleMatchedExpansion : MatchedExpansionData :=
  { innerOrder := 4, outerOrder := 5, matchingError := 3 }

example : matchedExpansionReady sampleMatchedExpansion := by
  norm_num [matchedExpansionReady, positiveOrders, matchingErrorControlled, sampleMatchedExpansion]

example : matchedOrderBudget sampleMatchedExpansion = 12 := by
  native_decide

/-- Finite executable readiness audit for matched expansion data. -/
def matchedExpansionDataListReady
    (data : List MatchedExpansionData) : Bool :=
  data.all fun d =>
    0 < d.innerOrder &&
      0 < d.outerOrder && d.matchingError ≤ d.innerOrder + d.outerOrder

theorem matchedExpansionDataList_readyWindow :
    matchedExpansionDataListReady
      [{ innerOrder := 2, outerOrder := 3, matchingError := 2 },
       { innerOrder := 4, outerOrder := 5, matchingError := 3 }] = true := by
  unfold matchedExpansionDataListReady
  native_decide

structure MatchedExpansionWindow where
  innerOrder : ℕ
  outerOrder : ℕ
  matchingError : ℕ
  overlapTerms : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MatchedExpansionWindow.ordersReady (w : MatchedExpansionWindow) : Prop :=
  0 < w.innerOrder ∧ 0 < w.outerOrder

def MatchedExpansionWindow.errorControlled (w : MatchedExpansionWindow) : Prop :=
  w.matchingError ≤ w.innerOrder + w.outerOrder + w.slack

def MatchedExpansionWindow.overlapControlled (w : MatchedExpansionWindow) : Prop :=
  w.overlapTerms ≤ w.innerOrder + w.outerOrder + w.slack

def MatchedExpansionWindow.ready (w : MatchedExpansionWindow) : Prop :=
  w.ordersReady ∧ w.errorControlled ∧ w.overlapControlled

def MatchedExpansionWindow.certificate (w : MatchedExpansionWindow) : ℕ :=
  w.innerOrder + w.outerOrder + w.matchingError + w.overlapTerms + w.slack

theorem overlapTerms_le_certificate (w : MatchedExpansionWindow) :
    w.overlapTerms ≤ w.certificate := by
  unfold MatchedExpansionWindow.certificate
  omega

def sampleMatchedExpansionWindow : MatchedExpansionWindow :=
  { innerOrder := 4, outerOrder := 5, matchingError := 3, overlapTerms := 6, slack := 0 }

example : sampleMatchedExpansionWindow.ready := by
  norm_num [sampleMatchedExpansionWindow, MatchedExpansionWindow.ready,
    MatchedExpansionWindow.ordersReady, MatchedExpansionWindow.errorControlled,
    MatchedExpansionWindow.overlapControlled]

/-- A refinement certificate for matched expansion windows. -/
structure MatchedExpansionCertificate where
  innerWindow : ℕ
  outerWindow : ℕ
  matchingErrorWindow : ℕ
  overlapWindow : ℕ
  slack : ℕ

/-- Expansion orders are positive and control matching and overlap. -/
def matchedExpansionCertificateControlled
    (w : MatchedExpansionCertificate) : Prop :=
  0 < w.innerWindow ∧
    0 < w.outerWindow ∧
      w.matchingErrorWindow ≤ w.innerWindow + w.outerWindow + w.slack ∧
        w.overlapWindow ≤ w.innerWindow + w.outerWindow + w.slack

/-- Readiness for a matched expansion certificate. -/
def matchedExpansionCertificateReady
    (w : MatchedExpansionCertificate) : Prop :=
  matchedExpansionCertificateControlled w ∧
    w.overlapWindow ≤
      w.innerWindow + w.outerWindow + w.matchingErrorWindow +
        w.overlapWindow + w.slack

/-- Total size of a matched expansion certificate. -/
def matchedExpansionCertificateSize
    (w : MatchedExpansionCertificate) : ℕ :=
  w.innerWindow + w.outerWindow + w.matchingErrorWindow + w.overlapWindow + w.slack

theorem matchedExpansionCertificate_overlap_le_size
    (w : MatchedExpansionCertificate)
    (h : matchedExpansionCertificateReady w) :
    w.overlapWindow ≤ matchedExpansionCertificateSize w := by
  rcases h with ⟨_, hbudget⟩
  unfold matchedExpansionCertificateSize
  omega

def sampleMatchedExpansionCertificate : MatchedExpansionCertificate where
  innerWindow := 4
  outerWindow := 5
  matchingErrorWindow := 3
  overlapWindow := 6
  slack := 0

example :
    matchedExpansionCertificateReady sampleMatchedExpansionCertificate := by
  norm_num [matchedExpansionCertificateReady,
    matchedExpansionCertificateControlled, sampleMatchedExpansionCertificate]

example :
    sampleMatchedExpansionCertificate.overlapWindow ≤
      matchedExpansionCertificateSize sampleMatchedExpansionCertificate := by
  apply matchedExpansionCertificate_overlap_le_size
  norm_num [matchedExpansionCertificateReady,
    matchedExpansionCertificateControlled, sampleMatchedExpansionCertificate]

/-- A refinement certificate with the matched-expansion budget separated from size. -/
structure MatchedExpansionRefinementCertificate where
  innerWindow : ℕ
  outerWindow : ℕ
  matchingErrorWindow : ℕ
  overlapWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MatchedExpansionRefinementCertificate.expansionControlled
    (cert : MatchedExpansionRefinementCertificate) : Prop :=
  0 < cert.innerWindow ∧
    0 < cert.outerWindow ∧
      cert.matchingErrorWindow ≤ cert.innerWindow + cert.outerWindow + cert.slack ∧
        cert.overlapWindow ≤ cert.innerWindow + cert.outerWindow + cert.slack

def MatchedExpansionRefinementCertificate.budgetControlled
    (cert : MatchedExpansionRefinementCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.innerWindow + cert.outerWindow + cert.matchingErrorWindow +
      cert.overlapWindow + cert.slack

def matchedExpansionRefinementReady
    (cert : MatchedExpansionRefinementCertificate) : Prop :=
  cert.expansionControlled ∧ cert.budgetControlled

def MatchedExpansionRefinementCertificate.size
    (cert : MatchedExpansionRefinementCertificate) : ℕ :=
  cert.innerWindow + cert.outerWindow + cert.matchingErrorWindow +
    cert.overlapWindow + cert.slack

theorem matchedExpansion_certificateBudgetWindow_le_size
    (cert : MatchedExpansionRefinementCertificate)
    (h : matchedExpansionRefinementReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleMatchedExpansionRefinementCertificate :
    MatchedExpansionRefinementCertificate :=
  { innerWindow := 4, outerWindow := 5, matchingErrorWindow := 3,
    overlapWindow := 6, certificateBudgetWindow := 18, slack := 0 }

example :
    matchedExpansionRefinementReady sampleMatchedExpansionRefinementCertificate := by
  norm_num [matchedExpansionRefinementReady,
    MatchedExpansionRefinementCertificate.expansionControlled,
    MatchedExpansionRefinementCertificate.budgetControlled,
    sampleMatchedExpansionRefinementCertificate]

example :
    sampleMatchedExpansionRefinementCertificate.certificateBudgetWindow ≤
      sampleMatchedExpansionRefinementCertificate.size := by
  apply matchedExpansion_certificateBudgetWindow_le_size
  norm_num [matchedExpansionRefinementReady,
    MatchedExpansionRefinementCertificate.expansionControlled,
    MatchedExpansionRefinementCertificate.budgetControlled,
    sampleMatchedExpansionRefinementCertificate]


structure MatchedExpansionSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MatchedExpansionSchemasBudgetCertificate.controlled
    (c : MatchedExpansionSchemasBudgetCertificate) : Prop :=
  0 < c.primaryWindow ∧ c.secondaryWindow ≤ c.primaryWindow + c.slack

def MatchedExpansionSchemasBudgetCertificate.budgetControlled
    (c : MatchedExpansionSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def MatchedExpansionSchemasBudgetCertificate.Ready
    (c : MatchedExpansionSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def MatchedExpansionSchemasBudgetCertificate.size
    (c : MatchedExpansionSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem matchedExpansionSchemas_budgetCertificate_le_size
    (c : MatchedExpansionSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleMatchedExpansionSchemasBudgetCertificate :
    MatchedExpansionSchemasBudgetCertificate :=
  { primaryWindow := 5
    secondaryWindow := 6
    certificateBudgetWindow := 12
    slack := 1 }

example : sampleMatchedExpansionSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [MatchedExpansionSchemasBudgetCertificate.controlled,
      sampleMatchedExpansionSchemasBudgetCertificate]
  · norm_num [MatchedExpansionSchemasBudgetCertificate.budgetControlled,
      sampleMatchedExpansionSchemasBudgetCertificate]

example :
    sampleMatchedExpansionSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleMatchedExpansionSchemasBudgetCertificate.size := by
  apply matchedExpansionSchemas_budgetCertificate_le_size
  constructor
  · norm_num [MatchedExpansionSchemasBudgetCertificate.controlled,
      sampleMatchedExpansionSchemasBudgetCertificate]
  · norm_num [MatchedExpansionSchemasBudgetCertificate.budgetControlled,
      sampleMatchedExpansionSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleMatchedExpansionSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [MatchedExpansionSchemasBudgetCertificate.controlled,
      sampleMatchedExpansionSchemasBudgetCertificate]
  · norm_num [MatchedExpansionSchemasBudgetCertificate.budgetControlled,
      sampleMatchedExpansionSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleMatchedExpansionSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleMatchedExpansionSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List MatchedExpansionSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleMatchedExpansionSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleMatchedExpansionSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.MatchedExpansionSchemas
