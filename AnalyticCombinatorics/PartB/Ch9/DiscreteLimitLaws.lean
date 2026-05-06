import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Discrete limit laws.
-/

namespace AnalyticCombinatorics.PartB.Ch9.DiscreteLimitLaws

/-- Bernoulli mass with rational parameter numerator `pNum / pDen`. -/
def bernoulliMassQ (pNum pDen k : ℕ) : ℚ :=
  if k = 0 then (pDen - pNum : ℚ) / pDen
  else if k = 1 then (pNum : ℚ) / pDen
  else 0

/-- Finite nonnegative mass audit on a sampled support. -/
def massNonnegativeUpTo (mass : ℕ → ℚ) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun k => 0 ≤ mass k

/-- Finite total mass over a prefix. -/
def massPrefixQ (mass : ℕ → ℚ) (N : ℕ) : ℚ :=
  (List.range (N + 1)).foldl (fun total k => total + mass k) 0

def DiscreteLawWindow (mass : ℕ → ℚ) (N : ℕ) : Prop :=
  massNonnegativeUpTo mass N = true ∧ massPrefixQ mass N = 1

theorem fairBernoulli_discreteWindow :
    DiscreteLawWindow (bernoulliMassQ 1 2) 1 := by
  unfold DiscreteLawWindow massNonnegativeUpTo massPrefixQ bernoulliMassQ
  native_decide

/-- First moment of a finite discrete distribution prefix. -/
def discreteFirstMomentQ (mass : ℕ → ℚ) (N : ℕ) : ℚ :=
  (List.range (N + 1)).foldl
    (fun (total : ℚ) (k : ℕ) => total + k * mass k) 0

def DiscreteFirstMomentWindow (mass : ℕ → ℚ) (N : ℕ) (moment : ℚ) : Prop :=
  discreteFirstMomentQ mass N = moment

theorem fairBernoulli_firstMomentWindow :
    DiscreteFirstMomentWindow (bernoulliMassQ 1 2) 1 (1 / 2) := by
  unfold DiscreteFirstMomentWindow discreteFirstMomentQ bernoulliMassQ
  native_decide

example : bernoulliMassQ 1 2 0 = 1 / 2 := by
  unfold bernoulliMassQ
  native_decide

example : massPrefixQ (bernoulliMassQ 1 2) 1 = 1 := by
  unfold massPrefixQ bernoulliMassQ
  native_decide

structure DiscreteLimitLawsBudgetCertificate where
  supportWindow : ℕ
  massWindow : ℕ
  convergenceWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DiscreteLimitLawsBudgetCertificate.controlled
    (c : DiscreteLimitLawsBudgetCertificate) : Prop :=
  0 < c.supportWindow ∧
    c.convergenceWindow ≤ c.supportWindow + c.massWindow + c.slack

def DiscreteLimitLawsBudgetCertificate.budgetControlled
    (c : DiscreteLimitLawsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.supportWindow + c.massWindow + c.convergenceWindow + c.slack

def DiscreteLimitLawsBudgetCertificate.Ready
    (c : DiscreteLimitLawsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def DiscreteLimitLawsBudgetCertificate.size
    (c : DiscreteLimitLawsBudgetCertificate) : ℕ :=
  c.supportWindow + c.massWindow + c.convergenceWindow + c.slack

theorem discreteLimitLaws_budgetCertificate_le_size
    (c : DiscreteLimitLawsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleDiscreteLimitLawsBudgetCertificate :
    DiscreteLimitLawsBudgetCertificate :=
  { supportWindow := 5
    massWindow := 6
    convergenceWindow := 10
    certificateBudgetWindow := 22
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleDiscreteLimitLawsBudgetCertificate.Ready := by
  constructor
  · norm_num [DiscreteLimitLawsBudgetCertificate.controlled,
      sampleDiscreteLimitLawsBudgetCertificate]
  · norm_num [DiscreteLimitLawsBudgetCertificate.budgetControlled,
      sampleDiscreteLimitLawsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleDiscreteLimitLawsBudgetCertificate.certificateBudgetWindow ≤
      sampleDiscreteLimitLawsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleDiscreteLimitLawsBudgetCertificate.Ready := by
  constructor
  · norm_num [DiscreteLimitLawsBudgetCertificate.controlled,
      sampleDiscreteLimitLawsBudgetCertificate]
  · norm_num [DiscreteLimitLawsBudgetCertificate.budgetControlled,
      sampleDiscreteLimitLawsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List DiscreteLimitLawsBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleDiscreteLimitLawsBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleDiscreteLimitLawsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch9.DiscreteLimitLaws
