import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite stack models.

Stacks are represented by lists with the head as the top.  This file records
small load and height calculations for recursive combinatorial processes.
-/

namespace AnalyticCombinatorics.AppA.FiniteStackModels

def push (x : ℕ) (xs : List ℕ) : List ℕ :=
  x :: xs

def pop (xs : List ℕ) : List ℕ :=
  xs.drop 1

def stackHeight (xs : List ℕ) : ℕ :=
  xs.length

def stackLoad (xs : List ℕ) : ℕ :=
  xs.sum

theorem stackHeight_push (x : ℕ) (xs : List ℕ) :
    stackHeight (push x xs) = stackHeight xs + 1 := by
  simp [stackHeight, push]

theorem stackLoad_push (x : ℕ) (xs : List ℕ) :
    stackLoad (push x xs) = x + stackLoad xs := by
  simp [stackLoad, push]

theorem pop_nil :
    pop [] = [] := by
  rfl

def sampleStack : List ℕ :=
  [5, 3, 1]

example : push 7 sampleStack = [7, 5, 3, 1] := by
  native_decide

example : pop sampleStack = [3, 1] := by
  native_decide

example : stackLoad sampleStack = 9 := by
  native_decide

structure StackWindow where
  height : ℕ
  pushes : ℕ
  pops : ℕ
  load : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def StackWindow.heightControlled (w : StackWindow) : Prop :=
  w.height + w.pops ≤ w.pushes + w.slack

def StackWindow.loadControlled (w : StackWindow) : Prop :=
  w.load ≤ w.height * (w.load + 1) + w.slack

def StackWindow.ready (w : StackWindow) : Prop :=
  w.heightControlled ∧ w.loadControlled

def StackWindow.certificate (w : StackWindow) : ℕ :=
  w.height + w.pushes + w.pops + w.load + w.slack

theorem height_le_certificate (w : StackWindow) :
    w.height ≤ w.certificate := by
  unfold StackWindow.certificate
  omega

def sampleStackWindow : StackWindow :=
  { height := 3, pushes := 4, pops := 1, load := 9, slack := 0 }

example : sampleStackWindow.ready := by
  norm_num [sampleStackWindow, StackWindow.ready,
    StackWindow.heightControlled, StackWindow.loadControlled]


structure FiniteStackModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteStackModelsBudgetCertificate.controlled
    (c : FiniteStackModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteStackModelsBudgetCertificate.budgetControlled
    (c : FiniteStackModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteStackModelsBudgetCertificate.Ready
    (c : FiniteStackModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteStackModelsBudgetCertificate.size
    (c : FiniteStackModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteStackModels_budgetCertificate_le_size
    (c : FiniteStackModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteStackModelsBudgetCertificate :
    FiniteStackModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleFiniteStackModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteStackModelsBudgetCertificate.controlled,
      sampleFiniteStackModelsBudgetCertificate]
  · norm_num [FiniteStackModelsBudgetCertificate.budgetControlled,
      sampleFiniteStackModelsBudgetCertificate]

example :
    sampleFiniteStackModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteStackModelsBudgetCertificate.size := by
  apply finiteStackModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteStackModelsBudgetCertificate.controlled,
      sampleFiniteStackModelsBudgetCertificate]
  · norm_num [FiniteStackModelsBudgetCertificate.budgetControlled,
      sampleFiniteStackModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleFiniteStackModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteStackModelsBudgetCertificate.controlled,
      sampleFiniteStackModelsBudgetCertificate]
  · norm_num [FiniteStackModelsBudgetCertificate.budgetControlled,
      sampleFiniteStackModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteStackModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteStackModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List FiniteStackModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteStackModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteStackModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteStackModels
