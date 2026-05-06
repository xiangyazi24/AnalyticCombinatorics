import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Powerset count checks.

This module models the finite PSET construction for a ground type `Fin n`.
-/

namespace AnalyticCombinatorics.PartA.Ch1.Powerset

def powersetCount (n : ℕ) : ℕ := 2 ^ n

def finitePowerset (n : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Fin n)).powerset

def finitePowersetCount (n : ℕ) : ℕ :=
  (finitePowerset n).card

def singletonSubsets (n : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Fin n)).image fun i => ({i} : Finset (Fin n))

def singletonSubsetCount (n : ℕ) : ℕ :=
  (singletonSubsets n).card

def subsetSizeLayer (n k : ℕ) : Finset (Finset (Fin n)) :=
  (finitePowerset n).filter fun s => s.card = k

def subsetSizeLayerCount (n k : ℕ) : ℕ :=
  (subsetSizeLayer n k).card

def subsetChoiceBudget (groundSize markedSlack : ℕ) : ℕ :=
  powersetCount groundSize + markedSlack

structure PowersetWindow where
  groundSize : ℕ
  markedSubsets : ℕ
  markedSlack : ℕ
deriving DecidableEq, Repr

def nonemptyGround (w : PowersetWindow) : Prop :=
  0 < w.groundSize

def markedSubsetsControlled (w : PowersetWindow) : Prop :=
  w.markedSubsets ≤ powersetCount w.groundSize + w.markedSlack

def powersetWindowReady (w : PowersetWindow) : Prop :=
  nonemptyGround w ∧ markedSubsetsControlled w

def powersetWindowBudget (w : PowersetWindow) : ℕ :=
  w.groundSize + w.markedSubsets + w.markedSlack

theorem powersetWindowReady.certificate {w : PowersetWindow}
    (h : powersetWindowReady w) :
    nonemptyGround w ∧ markedSubsetsControlled w ∧
      w.groundSize ≤ powersetWindowBudget w := by
  rcases h with ⟨hground, hcontrolled⟩
  refine ⟨hground, hcontrolled, ?_⟩
  unfold powersetWindowBudget
  omega

theorem markedSlack_le_budget (w : PowersetWindow) :
    w.markedSlack ≤ powersetWindowBudget w := by
  unfold powersetWindowBudget
  omega

theorem subset_mem_finitePowerset {n : ℕ} {s : Finset (Fin n)} :
    s ∈ finitePowerset n := by
  unfold finitePowerset
  exact Finset.mem_powerset.mpr (by intro x hx; exact Finset.mem_univ x)

theorem layer_member_card {n k : ℕ} {s : Finset (Fin n)}
    (h : s ∈ subsetSizeLayer n k) :
    s.card = k := by
  exact (Finset.mem_filter.mp h).2

def samplePowersetWindow : PowersetWindow :=
  { groundSize := 5, markedSubsets := 12, markedSlack := 4 }

example : powersetWindowReady samplePowersetWindow := by
  norm_num [powersetWindowReady, nonemptyGround]
  norm_num [markedSubsetsControlled, powersetCount, samplePowersetWindow]

example : powersetCount 0 = 1 := by native_decide
example : powersetCount 5 = 32 := by native_decide
example : powersetCount 10 = 1024 := by native_decide
example : subsetChoiceBudget 4 3 = 19 := by native_decide
example : powersetWindowBudget samplePowersetWindow = 21 := by native_decide
example : finitePowersetCount 0 = 1 := by native_decide
example : finitePowersetCount 3 = 8 := by native_decide
example : finitePowersetCount 5 = powersetCount 5 := by native_decide
example : singletonSubsetCount 4 = 4 := by native_decide
example : subsetSizeLayerCount 4 2 = 6 := by native_decide


structure PowersetBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PowersetBudgetCertificate.controlled
    (c : PowersetBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def PowersetBudgetCertificate.budgetControlled
    (c : PowersetBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def PowersetBudgetCertificate.Ready
    (c : PowersetBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PowersetBudgetCertificate.size
    (c : PowersetBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem powerset_budgetCertificate_le_size
    (c : PowersetBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def samplePowersetBudgetCertificate :
    PowersetBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : samplePowersetBudgetCertificate.Ready := by
  constructor
  · norm_num [PowersetBudgetCertificate.controlled,
      samplePowersetBudgetCertificate]
  · norm_num [PowersetBudgetCertificate.budgetControlled,
      samplePowersetBudgetCertificate]

example :
    samplePowersetBudgetCertificate.certificateBudgetWindow ≤
      samplePowersetBudgetCertificate.size := by
  apply powerset_budgetCertificate_le_size
  constructor
  · norm_num [PowersetBudgetCertificate.controlled,
      samplePowersetBudgetCertificate]
  · norm_num [PowersetBudgetCertificate.budgetControlled,
      samplePowersetBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    samplePowersetBudgetCertificate.Ready := by
  constructor
  · norm_num [PowersetBudgetCertificate.controlled,
      samplePowersetBudgetCertificate]
  · norm_num [PowersetBudgetCertificate.budgetControlled,
      samplePowersetBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    samplePowersetBudgetCertificate.certificateBudgetWindow ≤
      samplePowersetBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List PowersetBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [samplePowersetBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady samplePowersetBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.Powerset
