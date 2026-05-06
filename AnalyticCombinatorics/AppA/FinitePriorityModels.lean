import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite priority models.

Priority queues are represented as lists of priorities; the definitions keep
small load and threshold calculations executable.
-/

namespace AnalyticCombinatorics.AppA.FinitePriorityModels

def highPriorityCount (threshold : ℕ) (xs : List ℕ) : ℕ :=
  xs.filter (fun x => threshold ≤ x) |>.length

def priorityMass (xs : List ℕ) : ℕ :=
  xs.sum

def priorityBudgeted (xs : List ℕ) (budget : ℕ) : Prop :=
  priorityMass xs ≤ budget

theorem highPriorityCount_nil (threshold : ℕ) :
    highPriorityCount threshold [] = 0 := by
  rfl

theorem priorityMass_cons (x : ℕ) (xs : List ℕ) :
    priorityMass (x :: xs) = x + priorityMass xs := by
  simp [priorityMass]

theorem priorityBudgeted_mono {xs : List ℕ} {b c : ℕ}
    (h : priorityBudgeted xs b) (hbc : b ≤ c) :
    priorityBudgeted xs c := by
  unfold priorityBudgeted at *
  omega

def samplePriorities : List ℕ :=
  [4, 1, 7, 3, 7]

example : highPriorityCount 4 samplePriorities = 3 := by
  native_decide

example : priorityMass samplePriorities = 22 := by
  native_decide

example : priorityBudgeted samplePriorities 25 := by
  norm_num [priorityBudgeted, priorityMass, samplePriorities]

structure PriorityWindow where
  queueSize : ℕ
  highPriority : ℕ
  priorityMass : ℕ
  massBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PriorityWindow.countControlled (w : PriorityWindow) : Prop :=
  w.highPriority ≤ w.queueSize

def PriorityWindow.massControlled (w : PriorityWindow) : Prop :=
  w.priorityMass ≤ w.massBudget + w.slack

def PriorityWindow.ready (w : PriorityWindow) : Prop :=
  w.countControlled ∧ w.massControlled

def PriorityWindow.certificate (w : PriorityWindow) : ℕ :=
  w.queueSize + w.highPriority + w.priorityMass + w.massBudget + w.slack

theorem priorityMass_le_certificate (w : PriorityWindow) :
    w.priorityMass ≤ w.certificate := by
  unfold PriorityWindow.certificate
  omega

def samplePriorityWindow : PriorityWindow :=
  { queueSize := 5, highPriority := 3, priorityMass := 22, massBudget := 25, slack := 0 }

example : samplePriorityWindow.ready := by
  norm_num [samplePriorityWindow, PriorityWindow.ready,
    PriorityWindow.countControlled, PriorityWindow.massControlled]


structure FinitePriorityModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FinitePriorityModelsBudgetCertificate.controlled
    (c : FinitePriorityModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FinitePriorityModelsBudgetCertificate.budgetControlled
    (c : FinitePriorityModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FinitePriorityModelsBudgetCertificate.Ready
    (c : FinitePriorityModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FinitePriorityModelsBudgetCertificate.size
    (c : FinitePriorityModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finitePriorityModels_budgetCertificate_le_size
    (c : FinitePriorityModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFinitePriorityModelsBudgetCertificate :
    FinitePriorityModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleFinitePriorityModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FinitePriorityModelsBudgetCertificate.controlled,
      sampleFinitePriorityModelsBudgetCertificate]
  · norm_num [FinitePriorityModelsBudgetCertificate.budgetControlled,
      sampleFinitePriorityModelsBudgetCertificate]

example :
    sampleFinitePriorityModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFinitePriorityModelsBudgetCertificate.size := by
  apply finitePriorityModels_budgetCertificate_le_size
  constructor
  · norm_num [FinitePriorityModelsBudgetCertificate.controlled,
      sampleFinitePriorityModelsBudgetCertificate]
  · norm_num [FinitePriorityModelsBudgetCertificate.budgetControlled,
      sampleFinitePriorityModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleFinitePriorityModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FinitePriorityModelsBudgetCertificate.controlled,
      sampleFinitePriorityModelsBudgetCertificate]
  · norm_num [FinitePriorityModelsBudgetCertificate.budgetControlled,
      sampleFinitePriorityModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFinitePriorityModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFinitePriorityModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List FinitePriorityModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFinitePriorityModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFinitePriorityModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FinitePriorityModels
