import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite heap models.

Heaps are represented by arrays encoded as lists.  This file records small
index and load calculations for priority-queue style examples.
-/

namespace AnalyticCombinatorics.AppA.FiniteHeapModels

def parentIndex (n : ℕ) : ℕ :=
  (n - 1) / 2

def leftChildIndex (n : ℕ) : ℕ :=
  2 * n + 1

def rightChildIndex (n : ℕ) : ℕ :=
  2 * n + 2

def heapLoad (xs : List ℕ) : ℕ :=
  xs.sum

def heapSize (xs : List ℕ) : ℕ :=
  xs.length

theorem leftChildIndex_lt_rightChildIndex (n : ℕ) :
    leftChildIndex n < rightChildIndex n := by
  unfold leftChildIndex rightChildIndex
  omega

theorem heapSize_cons (x : ℕ) (xs : List ℕ) :
    heapSize (x :: xs) = heapSize xs + 1 := by
  simp [heapSize]

def sampleHeap : List ℕ :=
  [1, 3, 5, 7]

example : parentIndex 5 = 2 := by
  native_decide

example : leftChildIndex 3 = 7 := by
  native_decide

example : heapLoad sampleHeap = 16 := by
  native_decide

structure HeapWindow where
  heapSize : ℕ
  heapLoad : ℕ
  maxPriority : ℕ
  heightBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def HeapWindow.loadControlled (w : HeapWindow) : Prop :=
  w.heapLoad ≤ w.heapSize * w.maxPriority + w.slack

def HeapWindow.heightControlled (w : HeapWindow) : Prop :=
  w.heightBudget ≤ w.heapSize + w.slack

def HeapWindow.ready (w : HeapWindow) : Prop :=
  w.loadControlled ∧ w.heightControlled

def HeapWindow.certificate (w : HeapWindow) : ℕ :=
  w.heapSize + w.heapLoad + w.maxPriority + w.heightBudget + w.slack

theorem maxPriority_le_certificate (w : HeapWindow) :
    w.maxPriority ≤ w.certificate := by
  unfold HeapWindow.certificate
  omega

def sampleHeapWindow : HeapWindow :=
  { heapSize := 4, heapLoad := 16, maxPriority := 7, heightBudget := 3, slack := 0 }

example : sampleHeapWindow.ready := by
  norm_num [sampleHeapWindow, HeapWindow.ready, HeapWindow.loadControlled,
    HeapWindow.heightControlled]


structure FiniteHeapModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteHeapModelsBudgetCertificate.controlled
    (c : FiniteHeapModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteHeapModelsBudgetCertificate.budgetControlled
    (c : FiniteHeapModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteHeapModelsBudgetCertificate.Ready
    (c : FiniteHeapModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteHeapModelsBudgetCertificate.size
    (c : FiniteHeapModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteHeapModels_budgetCertificate_le_size
    (c : FiniteHeapModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteHeapModelsBudgetCertificate :
    FiniteHeapModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteHeapModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteHeapModelsBudgetCertificate.controlled,
      sampleFiniteHeapModelsBudgetCertificate]
  · norm_num [FiniteHeapModelsBudgetCertificate.budgetControlled,
      sampleFiniteHeapModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteHeapModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteHeapModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteHeapModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteHeapModelsBudgetCertificate.controlled,
      sampleFiniteHeapModelsBudgetCertificate]
  · norm_num [FiniteHeapModelsBudgetCertificate.budgetControlled,
      sampleFiniteHeapModelsBudgetCertificate]

example :
    sampleFiniteHeapModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteHeapModelsBudgetCertificate.size := by
  apply finiteHeapModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteHeapModelsBudgetCertificate.controlled,
      sampleFiniteHeapModelsBudgetCertificate]
  · norm_num [FiniteHeapModelsBudgetCertificate.budgetControlled,
      sampleFiniteHeapModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List FiniteHeapModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteHeapModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteHeapModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteHeapModels
