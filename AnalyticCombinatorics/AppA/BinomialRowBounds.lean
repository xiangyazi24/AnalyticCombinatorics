import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite binomial-row utilities.

These executable definitions support coefficient identities that are checked
row by row before being used in generating-function arguments.
-/

namespace AnalyticCombinatorics.AppA.BinomialRowBounds

def binomialRow (n : ℕ) : List ℕ :=
  (List.range (n + 1)).map (fun k => Nat.choose n k)

def binomialRowSum (n : ℕ) : ℕ :=
  (binomialRow n).sum

def rowBoundedBy (n bound : ℕ) : Prop :=
  ∀ k, k ≤ n → Nat.choose n k ≤ bound

theorem binomialRow_length (n : ℕ) :
    (binomialRow n).length = n + 1 := by
  simp [binomialRow]

theorem rowBoundedBy_zero :
    rowBoundedBy 0 1 := by
  intro k hk
  interval_cases k
  simp

theorem rowBoundedBy_mono {n b c : ℕ}
    (h : rowBoundedBy n b) (hbc : b ≤ c) :
    rowBoundedBy n c := by
  intro k hk
  exact le_trans (h k hk) hbc

example : binomialRow 4 = [1, 4, 6, 4, 1] := by
  native_decide

example : binomialRowSum 4 = 16 := by
  native_decide

example : rowBoundedBy 0 3 := by
  exact rowBoundedBy_mono rowBoundedBy_zero (by norm_num)

structure BinomialRowWindow where
  rowIndex : ℕ
  rowLength : ℕ
  rowMass : ℕ
  coefficientBound : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BinomialRowWindow.lengthReady (w : BinomialRowWindow) : Prop :=
  w.rowLength = w.rowIndex + 1

def BinomialRowWindow.massControlled (w : BinomialRowWindow) : Prop :=
  w.rowMass ≤ w.rowLength * w.coefficientBound + w.slack

def BinomialRowWindow.ready (w : BinomialRowWindow) : Prop :=
  w.lengthReady ∧ w.massControlled

def BinomialRowWindow.certificate (w : BinomialRowWindow) : ℕ :=
  w.rowIndex + w.rowLength + w.rowMass + w.coefficientBound + w.slack

theorem rowMass_le_certificate (w : BinomialRowWindow) :
    w.rowMass ≤ w.certificate := by
  unfold BinomialRowWindow.certificate
  omega

def sampleBinomialRowWindow : BinomialRowWindow :=
  { rowIndex := 4, rowLength := 5, rowMass := 16, coefficientBound := 6, slack := 0 }

example : sampleBinomialRowWindow.ready := by
  norm_num [sampleBinomialRowWindow, BinomialRowWindow.ready,
    BinomialRowWindow.lengthReady, BinomialRowWindow.massControlled]


structure BinomialRowBoundsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BinomialRowBoundsBudgetCertificate.controlled
    (c : BinomialRowBoundsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def BinomialRowBoundsBudgetCertificate.budgetControlled
    (c : BinomialRowBoundsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def BinomialRowBoundsBudgetCertificate.Ready
    (c : BinomialRowBoundsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BinomialRowBoundsBudgetCertificate.size
    (c : BinomialRowBoundsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem binomialRowBounds_budgetCertificate_le_size
    (c : BinomialRowBoundsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleBinomialRowBoundsBudgetCertificate :
    BinomialRowBoundsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleBinomialRowBoundsBudgetCertificate.Ready := by
  constructor
  · norm_num [BinomialRowBoundsBudgetCertificate.controlled,
      sampleBinomialRowBoundsBudgetCertificate]
  · norm_num [BinomialRowBoundsBudgetCertificate.budgetControlled,
      sampleBinomialRowBoundsBudgetCertificate]

example :
    sampleBinomialRowBoundsBudgetCertificate.certificateBudgetWindow ≤
      sampleBinomialRowBoundsBudgetCertificate.size := by
  apply binomialRowBounds_budgetCertificate_le_size
  constructor
  · norm_num [BinomialRowBoundsBudgetCertificate.controlled,
      sampleBinomialRowBoundsBudgetCertificate]
  · norm_num [BinomialRowBoundsBudgetCertificate.budgetControlled,
      sampleBinomialRowBoundsBudgetCertificate]

/-- Finite executable readiness audit for binomial-row certificates. -/
def binomialRowBoundsBudgetCertificateListReady
    (data : List BinomialRowBoundsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem binomialRowBoundsBudgetCertificateList_readyWindow :
    binomialRowBoundsBudgetCertificateListReady
      [sampleBinomialRowBoundsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold binomialRowBoundsBudgetCertificateListReady
    sampleBinomialRowBoundsBudgetCertificate
  native_decide

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleBinomialRowBoundsBudgetCertificate.Ready := by
  constructor
  · norm_num [BinomialRowBoundsBudgetCertificate.controlled,
      sampleBinomialRowBoundsBudgetCertificate]
  · norm_num [BinomialRowBoundsBudgetCertificate.budgetControlled,
      sampleBinomialRowBoundsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleBinomialRowBoundsBudgetCertificate.certificateBudgetWindow ≤
      sampleBinomialRowBoundsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List BinomialRowBoundsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleBinomialRowBoundsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleBinomialRowBoundsBudgetCertificate
  native_decide
end AnalyticCombinatorics.AppA.BinomialRowBounds
