import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Bloom filter limit schemas.

This module records finite occupancy-window bookkeeping for Bloom filters:
cell, hash, insertion, and false-positive certificate budgets.
-/

namespace AnalyticCombinatorics.PartB.Ch9.BloomFilterLimitSchemas

def emptyCellNumerator (cells hashes inserted : ℕ) : ℕ :=
  (cells - 1) ^ (hashes * inserted)

def emptyCellDenominator (cells hashes inserted : ℕ) : ℕ :=
  cells ^ (hashes * inserted)

theorem emptyCell_samples :
    emptyCellNumerator 4 2 1 = 9 ∧
    emptyCellDenominator 4 2 1 = 16 ∧
    emptyCellNumerator 10 2 3 = 531441 := by
  native_decide

structure BloomFilterLimitData where
  cells : ℕ
  hashes : ℕ
  inserted : ℕ
  falsePositiveWindow : ℕ
  occupancySlack : ℕ
deriving DecidableEq, Repr

def hasCells (d : BloomFilterLimitData) : Prop :=
  0 < d.cells

def hasHashes (d : BloomFilterLimitData) : Prop :=
  0 < d.hashes

def falsePositiveWindowControlled (d : BloomFilterLimitData) : Prop :=
  d.falsePositiveWindow ≤ d.hashes * (d.inserted + 1) + d.occupancySlack

def bloomFilterLimitReady (d : BloomFilterLimitData) : Prop :=
  hasCells d ∧ hasHashes d ∧ falsePositiveWindowControlled d

def bloomFilterLimitBudget (d : BloomFilterLimitData) : ℕ :=
  d.cells + d.hashes + d.inserted + d.falsePositiveWindow + d.occupancySlack

theorem bloomFilterLimitReady.cells
    {d : BloomFilterLimitData} (h : bloomFilterLimitReady d) :
    hasCells d := by
  exact h.1

theorem falsePositiveWindow_le_budget (d : BloomFilterLimitData) :
    d.falsePositiveWindow ≤ bloomFilterLimitBudget d := by
  unfold bloomFilterLimitBudget
  omega

def sampleBloomFilterLimitData : BloomFilterLimitData :=
  { cells := 10
    hashes := 2
    inserted := 3
    falsePositiveWindow := 8
    occupancySlack := 1 }

example : bloomFilterLimitReady sampleBloomFilterLimitData := by
  constructor
  · norm_num [hasCells, sampleBloomFilterLimitData]
  constructor
  · norm_num [hasHashes, sampleBloomFilterLimitData]
  · norm_num [falsePositiveWindowControlled, sampleBloomFilterLimitData]

example : bloomFilterLimitBudget sampleBloomFilterLimitData = 24 := by
  native_decide

/-- Finite executable readiness audit for Bloom-filter limit windows. -/
def bloomFilterLimitListReady
    (windows : List BloomFilterLimitData) : Bool :=
  windows.all fun d =>
    0 < d.cells &&
      0 < d.hashes &&
        d.falsePositiveWindow ≤ d.hashes * (d.inserted + 1) + d.occupancySlack

theorem bloomFilterLimitList_readyWindow :
    bloomFilterLimitListReady
      [{ cells := 4, hashes := 2, inserted := 1, falsePositiveWindow := 4,
         occupancySlack := 0 },
       { cells := 10, hashes := 2, inserted := 3, falsePositiveWindow := 8,
         occupancySlack := 1 }] = true := by
  unfold bloomFilterLimitListReady
  native_decide

structure BloomFilterLimitBudgetCertificate where
  cellWindow : ℕ
  hashWindow : ℕ
  insertionWindow : ℕ
  falsePositiveWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BloomFilterLimitBudgetCertificate.controlled
    (c : BloomFilterLimitBudgetCertificate) : Prop :=
  0 < c.cellWindow ∧
    0 < c.hashWindow ∧
      c.falsePositiveWindow ≤ c.hashWindow * (c.insertionWindow + 1) + c.slack

def BloomFilterLimitBudgetCertificate.budgetControlled
    (c : BloomFilterLimitBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.cellWindow + c.hashWindow + c.insertionWindow + c.falsePositiveWindow + c.slack

def BloomFilterLimitBudgetCertificate.Ready
    (c : BloomFilterLimitBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BloomFilterLimitBudgetCertificate.size
    (c : BloomFilterLimitBudgetCertificate) : ℕ :=
  c.cellWindow + c.hashWindow + c.insertionWindow + c.falsePositiveWindow + c.slack

theorem bloomFilterLimit_budgetCertificate_le_size
    (c : BloomFilterLimitBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleBloomFilterLimitBudgetCertificate :
    BloomFilterLimitBudgetCertificate :=
  { cellWindow := 10
    hashWindow := 2
    insertionWindow := 3
    falsePositiveWindow := 8
    certificateBudgetWindow := 24
    slack := 1 }

example : sampleBloomFilterLimitBudgetCertificate.Ready := by
  constructor
  · norm_num [BloomFilterLimitBudgetCertificate.controlled,
      sampleBloomFilterLimitBudgetCertificate]
  · norm_num [BloomFilterLimitBudgetCertificate.budgetControlled,
      sampleBloomFilterLimitBudgetCertificate]

example :
    sampleBloomFilterLimitBudgetCertificate.certificateBudgetWindow ≤
      sampleBloomFilterLimitBudgetCertificate.size := by
  apply bloomFilterLimit_budgetCertificate_le_size
  constructor
  · norm_num [BloomFilterLimitBudgetCertificate.controlled,
      sampleBloomFilterLimitBudgetCertificate]
  · norm_num [BloomFilterLimitBudgetCertificate.budgetControlled,
      sampleBloomFilterLimitBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleBloomFilterLimitBudgetCertificate.Ready := by
  constructor
  · norm_num [BloomFilterLimitBudgetCertificate.controlled,
      sampleBloomFilterLimitBudgetCertificate]
  · norm_num [BloomFilterLimitBudgetCertificate.budgetControlled,
      sampleBloomFilterLimitBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleBloomFilterLimitBudgetCertificate.certificateBudgetWindow ≤
      sampleBloomFilterLimitBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List BloomFilterLimitBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleBloomFilterLimitBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleBloomFilterLimitBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.BloomFilterLimitSchemas
