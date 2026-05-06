import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite queue models.

These definitions record list-based queue lengths and service budgets for
small combinatorial queueing examples.
-/

namespace AnalyticCombinatorics.AppA.FiniteQueueModels

def enqueue (x : ℕ) (q : List ℕ) : List ℕ :=
  q ++ [x]

def dequeue (q : List ℕ) : List ℕ :=
  q.drop 1

def queueLoad (q : List ℕ) : ℕ :=
  q.sum

def queueLength (q : List ℕ) : ℕ :=
  q.length

theorem queueLength_enqueue (x : ℕ) (q : List ℕ) :
    queueLength (enqueue x q) = queueLength q + 1 := by
  simp [queueLength, enqueue]

theorem queueLoad_enqueue (x : ℕ) (q : List ℕ) :
    queueLoad (enqueue x q) = queueLoad q + x := by
  simp [queueLoad, enqueue, Nat.add_comm]

theorem dequeue_nil :
    dequeue [] = [] := by
  rfl

def sampleQueue : List ℕ :=
  [2, 1, 4]

example : enqueue 3 sampleQueue = [2, 1, 4, 3] := by
  native_decide

example : dequeue sampleQueue = [1, 4] := by
  native_decide

example : queueLoad sampleQueue = 7 := by
  native_decide

structure QueueWindow where
  length : ℕ
  enqueues : ℕ
  dequeues : ℕ
  load : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def QueueWindow.lengthControlled (w : QueueWindow) : Prop :=
  w.length + w.dequeues ≤ w.enqueues + w.slack

def QueueWindow.loadControlled (w : QueueWindow) : Prop :=
  w.load ≤ w.length * (w.load + 1) + w.slack

def QueueWindow.ready (w : QueueWindow) : Prop :=
  w.lengthControlled ∧ w.loadControlled

def QueueWindow.certificate (w : QueueWindow) : ℕ :=
  w.length + w.enqueues + w.dequeues + w.load + w.slack

theorem dequeues_le_certificate (w : QueueWindow) :
    w.dequeues ≤ w.certificate := by
  unfold QueueWindow.certificate
  omega

def sampleQueueWindow : QueueWindow :=
  { length := 3, enqueues := 4, dequeues := 1, load := 7, slack := 0 }

example : sampleQueueWindow.ready := by
  norm_num [sampleQueueWindow, QueueWindow.ready,
    QueueWindow.lengthControlled, QueueWindow.loadControlled]


structure FiniteQueueModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteQueueModelsBudgetCertificate.controlled
    (c : FiniteQueueModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteQueueModelsBudgetCertificate.budgetControlled
    (c : FiniteQueueModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteQueueModelsBudgetCertificate.Ready
    (c : FiniteQueueModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteQueueModelsBudgetCertificate.size
    (c : FiniteQueueModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteQueueModels_budgetCertificate_le_size
    (c : FiniteQueueModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteQueueModelsBudgetCertificate :
    FiniteQueueModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleFiniteQueueModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteQueueModelsBudgetCertificate.controlled,
      sampleFiniteQueueModelsBudgetCertificate]
  · norm_num [FiniteQueueModelsBudgetCertificate.budgetControlled,
      sampleFiniteQueueModelsBudgetCertificate]

example :
    sampleFiniteQueueModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteQueueModelsBudgetCertificate.size := by
  apply finiteQueueModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteQueueModelsBudgetCertificate.controlled,
      sampleFiniteQueueModelsBudgetCertificate]
  · norm_num [FiniteQueueModelsBudgetCertificate.budgetControlled,
      sampleFiniteQueueModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleFiniteQueueModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteQueueModelsBudgetCertificate.controlled,
      sampleFiniteQueueModelsBudgetCertificate]
  · norm_num [FiniteQueueModelsBudgetCertificate.budgetControlled,
      sampleFiniteQueueModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteQueueModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteQueueModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List FiniteQueueModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteQueueModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteQueueModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteQueueModels
