import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Log-convexity schema bookkeeping.

The file records finite three-point convexity inequalities by cross
multiplication of natural budgets.
-/

namespace AnalyticCombinatorics.Asymptotics.LogConvexitySchemas

structure ThreePointData where
  left : ℕ
  middle : ℕ
  right : ℕ
deriving DecidableEq, Repr

def logConvexTriple (d : ThreePointData) : Prop :=
  d.middle * d.middle ≤ d.left * d.right

def positiveEndpoints (d : ThreePointData) : Prop :=
  0 < d.left ∧ 0 < d.right

def logConvexReady (d : ThreePointData) : Prop :=
  positiveEndpoints d ∧ logConvexTriple d

def endpointProduct (d : ThreePointData) : ℕ :=
  d.left * d.right

theorem logConvexReady.convex {d : ThreePointData}
    (h : logConvexReady d) :
    positiveEndpoints d ∧ logConvexTriple d ∧ d.middle * d.middle ≤ endpointProduct d := by
  refine ⟨h.1, h.2, ?_⟩
  simpa [endpointProduct, logConvexTriple] using h.2

def sampleLogConvex : ThreePointData :=
  { left := 2, middle := 3, right := 5 }

example : logConvexReady sampleLogConvex := by
  norm_num [logConvexReady, positiveEndpoints, logConvexTriple, sampleLogConvex]

example : endpointProduct sampleLogConvex = 10 := by
  native_decide

/-- Finite executable readiness audit for log-convex three-point data. -/
def logConvexDataListReady (data : List ThreePointData) : Bool :=
  data.all fun d =>
    0 < d.left && 0 < d.right && d.middle * d.middle ≤ d.left * d.right

theorem logConvexDataList_readyWindow :
    logConvexDataListReady
      [{ left := 1, middle := 2, right := 4 },
       { left := 2, middle := 3, right := 5 }] = true := by
  unfold logConvexDataListReady
  native_decide

structure LogConvexWindow where
  left : ℕ
  middle : ℕ
  right : ℕ
  convexitySlack : ℕ
deriving DecidableEq, Repr

def LogConvexWindow.positiveEndpoints (w : LogConvexWindow) : Prop :=
  0 < w.left ∧ 0 < w.right

def LogConvexWindow.convexControlled (w : LogConvexWindow) : Prop :=
  w.middle * w.middle ≤ w.left * w.right + w.convexitySlack

def LogConvexWindow.ready (w : LogConvexWindow) : Prop :=
  w.positiveEndpoints ∧ w.convexControlled

def LogConvexWindow.certificate (w : LogConvexWindow) : ℕ :=
  w.left + w.middle + w.right + w.convexitySlack

theorem middle_le_certificate (w : LogConvexWindow) :
    w.middle ≤ w.certificate := by
  unfold LogConvexWindow.certificate
  omega

def sampleLogConvexWindow : LogConvexWindow :=
  { left := 2, middle := 3, right := 5, convexitySlack := 0 }

example : sampleLogConvexWindow.ready := by
  norm_num [sampleLogConvexWindow, LogConvexWindow.ready,
    LogConvexWindow.positiveEndpoints, LogConvexWindow.convexControlled]

/-- A refinement certificate for log-convex windows. -/
structure LogConvexCertificate where
  leftWindow : ℕ
  middleWindow : ℕ
  rightWindow : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- The middle term is quadratically controlled by the endpoints. -/
def logConvexCertificateControlled
    (w : LogConvexCertificate) : Prop :=
  0 < w.leftWindow ∧
    0 < w.rightWindow ∧
      w.middleWindow * w.middleWindow ≤ w.leftWindow * w.rightWindow + w.slack

/-- Readiness for a log-convexity certificate. -/
def logConvexCertificateReady
    (w : LogConvexCertificate) : Prop :=
  logConvexCertificateControlled w ∧
    w.certificateBudget ≤ w.leftWindow + w.middleWindow + w.rightWindow + w.slack

/-- Total size of a log-convexity certificate. -/
def logConvexCertificateSize (w : LogConvexCertificate) : ℕ :=
  w.leftWindow + w.middleWindow + w.rightWindow + w.certificateBudget + w.slack

theorem logConvexCertificate_budget_le_size
    (w : LogConvexCertificate)
    (h : logConvexCertificateReady w) :
    w.certificateBudget ≤ logConvexCertificateSize w := by
  rcases h with ⟨_, hbudget⟩
  unfold logConvexCertificateSize
  omega

def sampleLogConvexCertificate : LogConvexCertificate where
  leftWindow := 2
  middleWindow := 3
  rightWindow := 5
  certificateBudget := 10
  slack := 0

example :
    logConvexCertificateReady sampleLogConvexCertificate := by
  norm_num [logConvexCertificateReady,
    logConvexCertificateControlled, sampleLogConvexCertificate]

example :
    sampleLogConvexCertificate.certificateBudget ≤
      logConvexCertificateSize sampleLogConvexCertificate := by
  apply logConvexCertificate_budget_le_size
  norm_num [logConvexCertificateReady,
    logConvexCertificateControlled, sampleLogConvexCertificate]

/-- A refinement certificate with the log-convexity budget separated from size. -/
structure LogConvexRefinementCertificate where
  leftWindow : ℕ
  middleWindow : ℕ
  rightWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ

def LogConvexRefinementCertificate.convexControlled
    (cert : LogConvexRefinementCertificate) : Prop :=
  0 < cert.leftWindow ∧
    0 < cert.rightWindow ∧
      cert.middleWindow * cert.middleWindow ≤
        cert.leftWindow * cert.rightWindow + cert.slack

def LogConvexRefinementCertificate.budgetControlled
    (cert : LogConvexRefinementCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.leftWindow + cert.middleWindow + cert.rightWindow + cert.slack

def logConvexRefinementReady
    (cert : LogConvexRefinementCertificate) : Prop :=
  cert.convexControlled ∧ cert.budgetControlled

def LogConvexRefinementCertificate.size
    (cert : LogConvexRefinementCertificate) : ℕ :=
  cert.leftWindow + cert.middleWindow + cert.rightWindow + cert.slack

theorem logConvex_certificateBudgetWindow_le_size
    (cert : LogConvexRefinementCertificate)
    (h : logConvexRefinementReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleLogConvexRefinementCertificate : LogConvexRefinementCertificate where
  leftWindow := 2
  middleWindow := 3
  rightWindow := 5
  certificateBudgetWindow := 10
  slack := 0

example : logConvexRefinementReady sampleLogConvexRefinementCertificate := by
  norm_num [logConvexRefinementReady,
    LogConvexRefinementCertificate.convexControlled,
    LogConvexRefinementCertificate.budgetControlled,
    sampleLogConvexRefinementCertificate]

example :
    sampleLogConvexRefinementCertificate.certificateBudgetWindow ≤
      sampleLogConvexRefinementCertificate.size := by
  apply logConvex_certificateBudgetWindow_le_size
  norm_num [logConvexRefinementReady,
    LogConvexRefinementCertificate.convexControlled,
    LogConvexRefinementCertificate.budgetControlled,
    sampleLogConvexRefinementCertificate]

structure LogConvexBudgetCertificate where
  leftWindow : ℕ
  middleWindow : ℕ
  rightWindow : ℕ
  convexBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LogConvexBudgetCertificate.controlled
    (c : LogConvexBudgetCertificate) : Prop :=
  0 < c.leftWindow ∧
    0 < c.rightWindow ∧
      c.middleWindow * c.middleWindow ≤ c.leftWindow * c.rightWindow + c.slack ∧
        c.convexBudgetWindow ≤
          c.leftWindow + c.middleWindow + c.rightWindow + c.slack

def LogConvexBudgetCertificate.budgetControlled
    (c : LogConvexBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.leftWindow + c.middleWindow + c.rightWindow +
      c.convexBudgetWindow + c.slack

def LogConvexBudgetCertificate.Ready
    (c : LogConvexBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LogConvexBudgetCertificate.size
    (c : LogConvexBudgetCertificate) : ℕ :=
  c.leftWindow + c.middleWindow + c.rightWindow +
    c.convexBudgetWindow + c.slack

theorem logConvex_budgetCertificate_le_size
    (c : LogConvexBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleLogConvexBudgetCertificate :
    LogConvexBudgetCertificate :=
  { leftWindow := 2
    middleWindow := 3
    rightWindow := 5
    convexBudgetWindow := 10
    certificateBudgetWindow := 20
    slack := 0 }

example : sampleLogConvexBudgetCertificate.Ready := by
  constructor
  · norm_num [LogConvexBudgetCertificate.controlled,
      sampleLogConvexBudgetCertificate]
  · norm_num [LogConvexBudgetCertificate.budgetControlled,
      sampleLogConvexBudgetCertificate]

example :
    sampleLogConvexBudgetCertificate.certificateBudgetWindow ≤
      sampleLogConvexBudgetCertificate.size := by
  apply logConvex_budgetCertificate_le_size
  constructor
  · norm_num [LogConvexBudgetCertificate.controlled,
      sampleLogConvexBudgetCertificate]
  · norm_num [LogConvexBudgetCertificate.budgetControlled,
      sampleLogConvexBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleLogConvexBudgetCertificate.Ready := by
  constructor
  · norm_num [LogConvexBudgetCertificate.controlled,
      sampleLogConvexBudgetCertificate]
  · norm_num [LogConvexBudgetCertificate.budgetControlled,
      sampleLogConvexBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleLogConvexBudgetCertificate.certificateBudgetWindow ≤
      sampleLogConvexBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List LogConvexBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleLogConvexBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleLogConvexBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.LogConvexitySchemas
