import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite cover models.

This file records simple finite set-cover bookkeeping for combinatorial
decompositions.
-/

namespace AnalyticCombinatorics.AppA.FiniteCoverModels

def coverBlockMass (blocks : List (List ℕ)) : ℕ :=
  blocks.map List.length |>.sum

def coverBlockCount (blocks : List (List ℕ)) : ℕ :=
  blocks.length

def elementCovered (x : ℕ) (blocks : List (List ℕ)) : Bool :=
  blocks.any (fun block => block.any (fun y => y == x))

def coverBudgeted (blocks : List (List ℕ)) (budget : ℕ) : Prop :=
  coverBlockMass blocks ≤ budget

theorem coverBlockMass_nil :
    coverBlockMass [] = 0 := by
  rfl

theorem coverBlockCount_cons (b : List ℕ) (blocks : List (List ℕ)) :
    coverBlockCount (b :: blocks) = coverBlockCount blocks + 1 := by
  simp [coverBlockCount]

def sampleCover : List (List ℕ) :=
  [[0, 1], [1, 2, 3], [4]]

example : coverBlockMass sampleCover = 6 := by
  native_decide

example : elementCovered 3 sampleCover = true := by
  native_decide

example : coverBudgeted sampleCover 8 := by
  norm_num [coverBudgeted, coverBlockMass, sampleCover]

structure CoverWindow where
  universeSize : ℕ
  blockCount : ℕ
  totalIncidences : ℕ
  coveredElements : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CoverWindow.coverageControlled (w : CoverWindow) : Prop :=
  w.coveredElements ≤ w.universeSize

def CoverWindow.incidenceControlled (w : CoverWindow) : Prop :=
  w.totalIncidences ≤ w.blockCount * w.universeSize + w.slack

def CoverWindow.ready (w : CoverWindow) : Prop :=
  w.coverageControlled ∧ w.incidenceControlled

def CoverWindow.certificate (w : CoverWindow) : ℕ :=
  w.universeSize + w.blockCount + w.totalIncidences + w.coveredElements + w.slack

theorem totalIncidences_le_certificate (w : CoverWindow) :
    w.totalIncidences ≤ w.certificate := by
  unfold CoverWindow.certificate
  omega

def sampleCoverWindow : CoverWindow :=
  { universeSize := 5, blockCount := 3, totalIncidences := 6, coveredElements := 5, slack := 0 }

example : sampleCoverWindow.ready := by
  norm_num [sampleCoverWindow, CoverWindow.ready, CoverWindow.coverageControlled,
    CoverWindow.incidenceControlled]


structure FiniteCoverModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteCoverModelsBudgetCertificate.controlled
    (c : FiniteCoverModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteCoverModelsBudgetCertificate.budgetControlled
    (c : FiniteCoverModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteCoverModelsBudgetCertificate.Ready
    (c : FiniteCoverModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteCoverModelsBudgetCertificate.size
    (c : FiniteCoverModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteCoverModels_budgetCertificate_le_size
    (c : FiniteCoverModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteCoverModelsBudgetCertificate :
    FiniteCoverModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteCoverModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteCoverModelsBudgetCertificate.controlled,
      sampleFiniteCoverModelsBudgetCertificate]
  · norm_num [FiniteCoverModelsBudgetCertificate.budgetControlled,
      sampleFiniteCoverModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteCoverModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteCoverModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteCoverModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteCoverModelsBudgetCertificate.controlled,
      sampleFiniteCoverModelsBudgetCertificate]
  · norm_num [FiniteCoverModelsBudgetCertificate.budgetControlled,
      sampleFiniteCoverModelsBudgetCertificate]

example :
    sampleFiniteCoverModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteCoverModelsBudgetCertificate.size := by
  apply finiteCoverModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteCoverModelsBudgetCertificate.controlled,
      sampleFiniteCoverModelsBudgetCertificate]
  · norm_num [FiniteCoverModelsBudgetCertificate.budgetControlled,
      sampleFiniteCoverModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List FiniteCoverModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteCoverModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteCoverModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteCoverModels
