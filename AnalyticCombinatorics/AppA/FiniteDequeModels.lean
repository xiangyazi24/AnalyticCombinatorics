import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite deque models.

Deques are list-encoded with front at the head.  This file records small
front/back updates and load calculations.
-/

namespace AnalyticCombinatorics.AppA.FiniteDequeModels

def pushFront (x : ℕ) (xs : List ℕ) : List ℕ :=
  x :: xs

def pushBack (x : ℕ) (xs : List ℕ) : List ℕ :=
  xs ++ [x]

def popFront (xs : List ℕ) : List ℕ :=
  xs.drop 1

def dequeSize (xs : List ℕ) : ℕ :=
  xs.length

def dequeLoad (xs : List ℕ) : ℕ :=
  xs.sum

theorem dequeSize_pushFront (x : ℕ) (xs : List ℕ) :
    dequeSize (pushFront x xs) = dequeSize xs + 1 := by
  simp [dequeSize, pushFront]

theorem dequeSize_pushBack (x : ℕ) (xs : List ℕ) :
    dequeSize (pushBack x xs) = dequeSize xs + 1 := by
  simp [dequeSize, pushBack]

def sampleDeque : List ℕ :=
  [2, 4, 6]

example : pushFront 1 sampleDeque = [1, 2, 4, 6] := by
  native_decide

example : pushBack 8 sampleDeque = [2, 4, 6, 8] := by
  native_decide

example : dequeLoad sampleDeque = 12 := by
  native_decide

structure DequeWindow where
  size : ℕ
  frontPushes : ℕ
  backPushes : ℕ
  pops : ℕ
  load : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DequeWindow.sizeControlled (w : DequeWindow) : Prop :=
  w.size + w.pops ≤ w.frontPushes + w.backPushes + w.slack

def DequeWindow.loadControlled (w : DequeWindow) : Prop :=
  w.load ≤ w.size * (w.load + 1) + w.slack

def DequeWindow.ready (w : DequeWindow) : Prop :=
  w.sizeControlled ∧ w.loadControlled

def DequeWindow.certificate (w : DequeWindow) : ℕ :=
  w.size + w.frontPushes + w.backPushes + w.pops + w.load + w.slack

theorem load_le_certificate (w : DequeWindow) :
    w.load ≤ w.certificate := by
  unfold DequeWindow.certificate
  omega

def sampleDequeWindow : DequeWindow :=
  { size := 3, frontPushes := 1, backPushes := 3, pops := 1, load := 12, slack := 0 }

example : sampleDequeWindow.ready := by
  norm_num [sampleDequeWindow, DequeWindow.ready, DequeWindow.sizeControlled,
    DequeWindow.loadControlled]


structure FiniteDequeModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteDequeModelsBudgetCertificate.controlled
    (c : FiniteDequeModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteDequeModelsBudgetCertificate.budgetControlled
    (c : FiniteDequeModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteDequeModelsBudgetCertificate.Ready
    (c : FiniteDequeModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteDequeModelsBudgetCertificate.size
    (c : FiniteDequeModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteDequeModels_budgetCertificate_le_size
    (c : FiniteDequeModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteDequeModelsBudgetCertificate :
    FiniteDequeModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteDequeModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteDequeModelsBudgetCertificate.controlled,
      sampleFiniteDequeModelsBudgetCertificate]
  · norm_num [FiniteDequeModelsBudgetCertificate.budgetControlled,
      sampleFiniteDequeModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteDequeModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteDequeModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteDequeModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteDequeModelsBudgetCertificate.controlled,
      sampleFiniteDequeModelsBudgetCertificate]
  · norm_num [FiniteDequeModelsBudgetCertificate.budgetControlled,
      sampleFiniteDequeModelsBudgetCertificate]

example :
    sampleFiniteDequeModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteDequeModelsBudgetCertificate.size := by
  apply finiteDequeModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteDequeModelsBudgetCertificate.controlled,
      sampleFiniteDequeModelsBudgetCertificate]
  · norm_num [FiniteDequeModelsBudgetCertificate.budgetControlled,
      sampleFiniteDequeModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List FiniteDequeModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteDequeModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteDequeModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteDequeModels
