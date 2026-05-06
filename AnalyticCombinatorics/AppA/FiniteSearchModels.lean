import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite search models.

The module records simple search-cost and predicate-filtering calculations
used in algorithmic combinatorics examples.
-/

namespace AnalyticCombinatorics.AppA.FiniteSearchModels

def firstMatchIndex (target : ℕ) (xs : List ℕ) : ℕ :=
  match xs.findIdx? (fun x => x == target) with
  | some i => i
  | none => xs.length

def matchCount (target : ℕ) (xs : List ℕ) : ℕ :=
  xs.filter (fun x => x == target) |>.length

def searchCost (target : ℕ) (xs : List ℕ) : ℕ :=
  firstMatchIndex target xs + 1

theorem matchCount_nil (target : ℕ) :
    matchCount target [] = 0 := by
  rfl

theorem firstMatchIndex_nil (target : ℕ) :
    firstMatchIndex target [] = 0 := by
  rfl

def sampleSearchList : List ℕ :=
  [5, 2, 7, 2, 9]

example : firstMatchIndex 2 sampleSearchList = 1 := by
  native_decide

example : matchCount 2 sampleSearchList = 2 := by
  native_decide

example : searchCost 7 sampleSearchList = 3 := by
  native_decide

structure SearchWindow where
  listLength : ℕ
  firstIndex : ℕ
  matchTotal : ℕ
  observedCost : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SearchWindow.indexControlled (w : SearchWindow) : Prop :=
  w.firstIndex ≤ w.listLength

def SearchWindow.costControlled (w : SearchWindow) : Prop :=
  w.observedCost ≤ w.listLength + 1 + w.slack

def SearchWindow.matchControlled (w : SearchWindow) : Prop :=
  w.matchTotal ≤ w.listLength

def SearchWindow.ready (w : SearchWindow) : Prop :=
  w.indexControlled ∧ w.costControlled ∧ w.matchControlled

def SearchWindow.certificate (w : SearchWindow) : ℕ :=
  w.listLength + w.firstIndex + w.matchTotal + w.observedCost + w.slack

theorem cost_le_certificate (w : SearchWindow) :
    w.observedCost ≤ w.certificate := by
  unfold SearchWindow.certificate
  omega

def sampleSearchWindow : SearchWindow :=
  { listLength := 5, firstIndex := 1, matchTotal := 2, observedCost := 2, slack := 0 }

example : sampleSearchWindow.ready := by
  norm_num [sampleSearchWindow, SearchWindow.ready, SearchWindow.indexControlled,
    SearchWindow.costControlled, SearchWindow.matchControlled]


structure FiniteSearchModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteSearchModelsBudgetCertificate.controlled
    (c : FiniteSearchModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteSearchModelsBudgetCertificate.budgetControlled
    (c : FiniteSearchModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteSearchModelsBudgetCertificate.Ready
    (c : FiniteSearchModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteSearchModelsBudgetCertificate.size
    (c : FiniteSearchModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteSearchModels_budgetCertificate_le_size
    (c : FiniteSearchModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteSearchModelsBudgetCertificate :
    FiniteSearchModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteSearchModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteSearchModelsBudgetCertificate.controlled,
      sampleFiniteSearchModelsBudgetCertificate]
  · norm_num [FiniteSearchModelsBudgetCertificate.budgetControlled,
      sampleFiniteSearchModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteSearchModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteSearchModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteSearchModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteSearchModelsBudgetCertificate.controlled,
      sampleFiniteSearchModelsBudgetCertificate]
  · norm_num [FiniteSearchModelsBudgetCertificate.budgetControlled,
      sampleFiniteSearchModelsBudgetCertificate]

example :
    sampleFiniteSearchModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteSearchModelsBudgetCertificate.size := by
  apply finiteSearchModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteSearchModelsBudgetCertificate.controlled,
      sampleFiniteSearchModelsBudgetCertificate]
  · norm_num [FiniteSearchModelsBudgetCertificate.budgetControlled,
      sampleFiniteSearchModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List FiniteSearchModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteSearchModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteSearchModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteSearchModels
