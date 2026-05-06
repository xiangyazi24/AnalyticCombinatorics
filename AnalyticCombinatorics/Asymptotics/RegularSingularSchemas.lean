import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Regular-singular differential schema bookkeeping.

This module records the finite order conditions that appear before applying
analytic transfer to solutions of singular differential equations.
-/

namespace AnalyticCombinatorics.Asymptotics.RegularSingularSchemas

structure RegularSingularData where
  leadingOrder : ℕ
  indicialGap : ℕ
  remainderOrder : ℕ
deriving DecidableEq, Repr

def regularSingularReady (d : RegularSingularData) : Prop :=
  0 < d.leadingOrder ∧ d.leadingOrder ≤ d.remainderOrder

def separatedIndicialRoots (d : RegularSingularData) : Prop :=
  0 < d.indicialGap

def totalOrderBudget (d : RegularSingularData) : ℕ :=
  d.leadingOrder + d.indicialGap + d.remainderOrder

theorem regularSingularReady.leading_pos {d : RegularSingularData}
    (h : regularSingularReady d) :
    0 < d.leadingOrder ∧ d.leadingOrder ≤ d.remainderOrder ∧
      d.leadingOrder ≤ totalOrderBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold totalOrderBudget
  omega

theorem totalOrderBudget_ge_leading (d : RegularSingularData) :
    d.leadingOrder ≤ totalOrderBudget d := by
  unfold totalOrderBudget
  omega

def sampleRegular : RegularSingularData :=
  { leadingOrder := 2, indicialGap := 3, remainderOrder := 5 }

example : regularSingularReady sampleRegular := by
  norm_num [regularSingularReady, sampleRegular]

example : separatedIndicialRoots sampleRegular := by
  norm_num [separatedIndicialRoots, sampleRegular]

example : totalOrderBudget sampleRegular = 10 := by
  native_decide

/-- Finite executable readiness audit for regular-singular data. -/
def regularSingularDataListReady
    (data : List RegularSingularData) : Bool :=
  data.all fun d =>
    0 < d.leadingOrder && 0 < d.indicialGap && d.leadingOrder ≤ d.remainderOrder

theorem regularSingularDataList_readyWindow :
    regularSingularDataListReady
      [{ leadingOrder := 1, indicialGap := 2, remainderOrder := 3 },
       { leadingOrder := 2, indicialGap := 3, remainderOrder := 5 }] = true := by
  unfold regularSingularDataListReady
  native_decide

structure RegularSingularWindow where
  leadingWindow : ℕ
  indicialWindow : ℕ
  remainderWindow : ℕ
  singularBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RegularSingularWindow.remainderControlled (w : RegularSingularWindow) : Prop :=
  w.leadingWindow ≤ w.remainderWindow + w.slack

def regularSingularWindowReady (w : RegularSingularWindow) : Prop :=
  0 < w.leadingWindow ∧ 0 < w.indicialWindow ∧ w.remainderControlled ∧
    w.singularBudget ≤ w.leadingWindow + w.indicialWindow + w.remainderWindow + w.slack

def RegularSingularWindow.certificate (w : RegularSingularWindow) : ℕ :=
  w.leadingWindow + w.indicialWindow + w.remainderWindow + w.singularBudget + w.slack

theorem regularSingular_singularBudget_le_certificate
    (w : RegularSingularWindow) :
    w.singularBudget ≤ w.certificate := by
  unfold RegularSingularWindow.certificate
  omega

def sampleRegularSingularWindow : RegularSingularWindow :=
  { leadingWindow := 2, indicialWindow := 3, remainderWindow := 5,
    singularBudget := 11, slack := 1 }

example : regularSingularWindowReady sampleRegularSingularWindow := by
  norm_num [regularSingularWindowReady,
    RegularSingularWindow.remainderControlled, sampleRegularSingularWindow]

/-- A refinement certificate for regular-singular windows. -/
structure RegularSingularCertificate where
  leadingWindow : ℕ
  indicialGapWindow : ℕ
  remainderWindow : ℕ
  singularBudgetWindow : ℕ
  slack : ℕ

/-- Leading order, indicial separation, and remainder control are finite. -/
def regularSingularCertificateControlled
    (w : RegularSingularCertificate) : Prop :=
  0 < w.leadingWindow ∧
    0 < w.indicialGapWindow ∧
      w.leadingWindow ≤ w.remainderWindow + w.slack ∧
        w.singularBudgetWindow ≤
          w.leadingWindow + w.indicialGapWindow + w.remainderWindow + w.slack

/-- Readiness for a regular-singular certificate. -/
def regularSingularCertificateReady
    (w : RegularSingularCertificate) : Prop :=
  regularSingularCertificateControlled w ∧
    w.singularBudgetWindow ≤
      w.leadingWindow + w.indicialGapWindow + w.remainderWindow +
        w.singularBudgetWindow + w.slack

/-- Total size of a regular-singular certificate. -/
def regularSingularCertificateSize
    (w : RegularSingularCertificate) : ℕ :=
  w.leadingWindow + w.indicialGapWindow + w.remainderWindow +
    w.singularBudgetWindow + w.slack

theorem regularSingularCertificate_budget_le_size
    (w : RegularSingularCertificate)
    (h : regularSingularCertificateReady w) :
    w.singularBudgetWindow ≤ regularSingularCertificateSize w := by
  rcases h with ⟨_, hbudget⟩
  unfold regularSingularCertificateSize
  omega

def sampleRegularSingularCertificate : RegularSingularCertificate where
  leadingWindow := 2
  indicialGapWindow := 3
  remainderWindow := 5
  singularBudgetWindow := 11
  slack := 1

example :
    regularSingularCertificateReady sampleRegularSingularCertificate := by
  norm_num [regularSingularCertificateReady,
    regularSingularCertificateControlled, sampleRegularSingularCertificate]

example :
    sampleRegularSingularCertificate.singularBudgetWindow ≤
      regularSingularCertificateSize sampleRegularSingularCertificate := by
  apply regularSingularCertificate_budget_le_size
  norm_num [regularSingularCertificateReady,
    regularSingularCertificateControlled, sampleRegularSingularCertificate]

/-- A refinement certificate with the regular-singular budget separated from size. -/
structure RegularSingularRefinementCertificate where
  leadingWindow : ℕ
  indicialGapWindow : ℕ
  remainderWindow : ℕ
  singularBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RegularSingularRefinementCertificate.orderControlled
    (cert : RegularSingularRefinementCertificate) : Prop :=
  0 < cert.leadingWindow ∧
    0 < cert.indicialGapWindow ∧
      cert.leadingWindow ≤ cert.remainderWindow + cert.slack ∧
        cert.singularBudgetWindow ≤
          cert.leadingWindow + cert.indicialGapWindow + cert.remainderWindow + cert.slack

def RegularSingularRefinementCertificate.budgetControlled
    (cert : RegularSingularRefinementCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.leadingWindow + cert.indicialGapWindow + cert.remainderWindow +
      cert.singularBudgetWindow + cert.slack

def regularSingularRefinementReady
    (cert : RegularSingularRefinementCertificate) : Prop :=
  cert.orderControlled ∧ cert.budgetControlled

def RegularSingularRefinementCertificate.size
    (cert : RegularSingularRefinementCertificate) : ℕ :=
  cert.leadingWindow + cert.indicialGapWindow + cert.remainderWindow +
    cert.singularBudgetWindow + cert.slack

theorem regularSingular_certificateBudgetWindow_le_size
    (cert : RegularSingularRefinementCertificate)
    (h : regularSingularRefinementReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRegularSingularRefinementCertificate :
    RegularSingularRefinementCertificate :=
  { leadingWindow := 2, indicialGapWindow := 3, remainderWindow := 5,
    singularBudgetWindow := 11, certificateBudgetWindow := 22, slack := 1 }

example :
    regularSingularRefinementReady sampleRegularSingularRefinementCertificate := by
  norm_num [regularSingularRefinementReady,
    RegularSingularRefinementCertificate.orderControlled,
    RegularSingularRefinementCertificate.budgetControlled,
    sampleRegularSingularRefinementCertificate]

example :
    sampleRegularSingularRefinementCertificate.certificateBudgetWindow ≤
      sampleRegularSingularRefinementCertificate.size := by
  apply regularSingular_certificateBudgetWindow_le_size
  norm_num [regularSingularRefinementReady,
    RegularSingularRefinementCertificate.orderControlled,
    RegularSingularRefinementCertificate.budgetControlled,
    sampleRegularSingularRefinementCertificate]


structure RegularSingularSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RegularSingularSchemasBudgetCertificate.controlled
    (c : RegularSingularSchemasBudgetCertificate) : Prop :=
  0 < c.primaryWindow ∧ c.secondaryWindow ≤ c.primaryWindow + c.slack

def RegularSingularSchemasBudgetCertificate.budgetControlled
    (c : RegularSingularSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def RegularSingularSchemasBudgetCertificate.Ready
    (c : RegularSingularSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RegularSingularSchemasBudgetCertificate.size
    (c : RegularSingularSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem regularSingularSchemas_budgetCertificate_le_size
    (c : RegularSingularSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRegularSingularSchemasBudgetCertificate :
    RegularSingularSchemasBudgetCertificate :=
  { primaryWindow := 5
    secondaryWindow := 6
    certificateBudgetWindow := 12
    slack := 1 }

example : sampleRegularSingularSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RegularSingularSchemasBudgetCertificate.controlled,
      sampleRegularSingularSchemasBudgetCertificate]
  · norm_num [RegularSingularSchemasBudgetCertificate.budgetControlled,
      sampleRegularSingularSchemasBudgetCertificate]

example :
    sampleRegularSingularSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRegularSingularSchemasBudgetCertificate.size := by
  apply regularSingularSchemas_budgetCertificate_le_size
  constructor
  · norm_num [RegularSingularSchemasBudgetCertificate.controlled,
      sampleRegularSingularSchemasBudgetCertificate]
  · norm_num [RegularSingularSchemasBudgetCertificate.budgetControlled,
      sampleRegularSingularSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleRegularSingularSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RegularSingularSchemasBudgetCertificate.controlled,
      sampleRegularSingularSchemasBudgetCertificate]
  · norm_num [RegularSingularSchemasBudgetCertificate.budgetControlled,
      sampleRegularSingularSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRegularSingularSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRegularSingularSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List RegularSingularSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRegularSingularSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleRegularSingularSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.RegularSingularSchemas
