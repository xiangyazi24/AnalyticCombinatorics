import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Local limit laws.
-/

namespace AnalyticCombinatorics.PartB.Ch9.LocalLimitLaws

/-- Binomial row mass numerator. -/
def binomialMassNumerator (n k : ℕ) : ℕ :=
  n.choose k

/-- Symmetry audit for a binomial local limit row. -/
def binomialSymmetryCheck (n : ℕ) : Bool :=
  (List.range (n + 1)).all fun k =>
    binomialMassNumerator n k = binomialMassNumerator n (n - k)

/-- Crude local envelope: each mass numerator is at most the row total. -/
def binomialLocalEnvelopeCheck (n : ℕ) : Bool :=
  (List.range (n + 1)).all fun k => binomialMassNumerator n k ≤ 2 ^ n

def LocalLimitWindow (n : ℕ) : Prop :=
  binomialSymmetryCheck n = true ∧ binomialLocalEnvelopeCheck n = true

theorem binomial_localLimitWindow_12 :
    LocalLimitWindow 12 := by
  unfold LocalLimitWindow binomialSymmetryCheck binomialLocalEnvelopeCheck
    binomialMassNumerator
  native_decide

/-- Prefix sum of a sampled binomial row. -/
def binomialRowPrefixSum (n N : ℕ) : ℕ :=
  (List.range (N + 1)).foldl
    (fun total k => total + binomialMassNumerator n k) 0

def BinomialRowMassWindow (n : ℕ) : Prop :=
  binomialRowPrefixSum n n = 2 ^ n

theorem binomialRowMass_window_8 :
    BinomialRowMassWindow 8 := by
  unfold BinomialRowMassWindow binomialRowPrefixSum binomialMassNumerator
  native_decide

structure LocalLimitLawsBudgetCertificate where
  latticeWindow : ℕ
  densityWindow : ℕ
  localErrorWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LocalLimitLawsBudgetCertificate.controlled
    (c : LocalLimitLawsBudgetCertificate) : Prop :=
  0 < c.latticeWindow ∧
    c.localErrorWindow ≤ c.latticeWindow + c.densityWindow + c.slack

def LocalLimitLawsBudgetCertificate.budgetControlled
    (c : LocalLimitLawsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.latticeWindow + c.densityWindow + c.localErrorWindow + c.slack

def LocalLimitLawsBudgetCertificate.Ready
    (c : LocalLimitLawsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LocalLimitLawsBudgetCertificate.size
    (c : LocalLimitLawsBudgetCertificate) : ℕ :=
  c.latticeWindow + c.densityWindow + c.localErrorWindow + c.slack

theorem localLimitLaws_budgetCertificate_le_size
    (c : LocalLimitLawsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleLocalLimitLawsBudgetCertificate :
    LocalLimitLawsBudgetCertificate :=
  { latticeWindow := 5
    densityWindow := 6
    localErrorWindow := 10
    certificateBudgetWindow := 22
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleLocalLimitLawsBudgetCertificate.Ready := by
  constructor
  · norm_num [LocalLimitLawsBudgetCertificate.controlled,
      sampleLocalLimitLawsBudgetCertificate]
  · norm_num [LocalLimitLawsBudgetCertificate.budgetControlled,
      sampleLocalLimitLawsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleLocalLimitLawsBudgetCertificate.certificateBudgetWindow ≤
      sampleLocalLimitLawsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleLocalLimitLawsBudgetCertificate.Ready := by
  constructor
  · norm_num [LocalLimitLawsBudgetCertificate.controlled,
      sampleLocalLimitLawsBudgetCertificate]
  · norm_num [LocalLimitLawsBudgetCertificate.budgetControlled,
      sampleLocalLimitLawsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List LocalLimitLawsBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleLocalLimitLawsBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleLocalLimitLawsBudgetCertificate
  native_decide

example :
    budgetCertificateListReady
      [sampleLocalLimitLawsBudgetCertificate] = true := by
  exact budgetCertificateList_readyWindow

end AnalyticCombinatorics.PartB.Ch9.LocalLimitLaws
