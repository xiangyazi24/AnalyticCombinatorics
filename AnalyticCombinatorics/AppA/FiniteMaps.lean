import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite map utilities for coefficient tables.

The constructions here model small table transformations used in symbolic
and coefficientwise arguments.
-/

namespace AnalyticCombinatorics.AppA.FiniteMaps

def tableLookup (default : ℕ) (xs : List (ℕ × ℕ)) (key : ℕ) : ℕ :=
  match xs.find? (fun pair => pair.1 == key) with
  | some pair => pair.2
  | none => default

def tableSupport (xs : List (ℕ × ℕ)) : List ℕ :=
  xs.map Prod.fst

def tableMass (xs : List (ℕ × ℕ)) : ℕ :=
  xs.map Prod.snd |>.sum

def valuesBoundedBy (xs : List (ℕ × ℕ)) (bound : ℕ) : Prop :=
  ∀ pair ∈ xs, pair.2 ≤ bound

theorem tableMass_nil :
    tableMass [] = 0 := by
  rfl

theorem tableMass_cons (pair : ℕ × ℕ) (xs : List (ℕ × ℕ)) :
    tableMass (pair :: xs) = pair.2 + tableMass xs := by
  simp [tableMass]

theorem valuesBoundedBy_mono {xs : List (ℕ × ℕ)} {b c : ℕ}
    (h : valuesBoundedBy xs b) (hbc : b ≤ c) :
    valuesBoundedBy xs c := by
  intro pair hp
  exact le_trans (h pair hp) hbc

def sampleTable : List (ℕ × ℕ) :=
  [(0, 4), (2, 7), (5, 1)]

example : tableLookup 9 sampleTable 2 = 7 := by
  native_decide

example : tableLookup 9 sampleTable 3 = 9 := by
  native_decide

example : tableMass sampleTable = 12 := by
  native_decide

structure TableWindow where
  entryCount : ℕ
  keyBudget : ℕ
  valueBudget : ℕ
  lookupBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TableWindow.lookupControlled (w : TableWindow) : Prop :=
  w.lookupBudget ≤ w.entryCount + w.keyBudget + w.valueBudget + w.slack

def tableWindowReady (w : TableWindow) : Prop :=
  0 < w.entryCount ∧
    w.lookupControlled

def TableWindow.certificate (w : TableWindow) : ℕ :=
  w.entryCount + w.keyBudget + w.valueBudget + w.slack

theorem tableWindow_lookupBudget_le_certificate {w : TableWindow}
    (h : tableWindowReady w) :
    w.lookupBudget ≤ w.certificate := by
  rcases h with ⟨_, hlookup⟩
  exact hlookup

def sampleTableWindow : TableWindow :=
  { entryCount := 3, keyBudget := 5, valueBudget := 12, lookupBudget := 19, slack := 0 }

example : tableWindowReady sampleTableWindow := by
  norm_num [tableWindowReady, TableWindow.lookupControlled, sampleTableWindow]

example : sampleTableWindow.certificate = 20 := by
  native_decide


structure FiniteMapsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteMapsBudgetCertificate.controlled
    (c : FiniteMapsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteMapsBudgetCertificate.budgetControlled
    (c : FiniteMapsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteMapsBudgetCertificate.Ready
    (c : FiniteMapsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteMapsBudgetCertificate.size
    (c : FiniteMapsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteMaps_budgetCertificate_le_size
    (c : FiniteMapsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteMapsBudgetCertificate :
    FiniteMapsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleFiniteMapsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteMapsBudgetCertificate.controlled,
      sampleFiniteMapsBudgetCertificate]
  · norm_num [FiniteMapsBudgetCertificate.budgetControlled,
      sampleFiniteMapsBudgetCertificate]

example :
    sampleFiniteMapsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteMapsBudgetCertificate.size := by
  apply finiteMaps_budgetCertificate_le_size
  constructor
  · norm_num [FiniteMapsBudgetCertificate.controlled,
      sampleFiniteMapsBudgetCertificate]
  · norm_num [FiniteMapsBudgetCertificate.budgetControlled,
      sampleFiniteMapsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleFiniteMapsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteMapsBudgetCertificate.controlled,
      sampleFiniteMapsBudgetCertificate]
  · norm_num [FiniteMapsBudgetCertificate.budgetControlled,
      sampleFiniteMapsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteMapsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteMapsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List FiniteMapsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteMapsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteMapsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteMaps
