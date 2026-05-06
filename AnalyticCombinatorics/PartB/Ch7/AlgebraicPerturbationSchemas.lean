import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Algebraic perturbation schemas.

The finite schema records algebraic degree, perturbation budget, and
stability slack.
-/

namespace AnalyticCombinatorics.PartB.Ch7.AlgebraicPerturbationSchemas

structure AlgebraicPerturbationData where
  algebraicDegree : ℕ
  perturbationBudget : ℕ
  stabilitySlack : ℕ
deriving DecidableEq, Repr

def algebraicDegreePositive (d : AlgebraicPerturbationData) : Prop :=
  0 < d.algebraicDegree

def perturbationControlled (d : AlgebraicPerturbationData) : Prop :=
  d.perturbationBudget ≤ d.algebraicDegree + d.stabilitySlack

def algebraicPerturbationReady (d : AlgebraicPerturbationData) : Prop :=
  algebraicDegreePositive d ∧ perturbationControlled d

def algebraicPerturbationBudget (d : AlgebraicPerturbationData) : ℕ :=
  d.algebraicDegree + d.perturbationBudget + d.stabilitySlack

theorem algebraicPerturbationReady.degree
    {d : AlgebraicPerturbationData}
    (h : algebraicPerturbationReady d) :
    algebraicDegreePositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem perturbationBudget_le_algebraicBudget
    (d : AlgebraicPerturbationData) :
    d.perturbationBudget ≤ algebraicPerturbationBudget d := by
  unfold algebraicPerturbationBudget
  omega

def sampleAlgebraicPerturbationData : AlgebraicPerturbationData :=
  { algebraicDegree := 4, perturbationBudget := 6, stabilitySlack := 3 }

example : algebraicPerturbationReady sampleAlgebraicPerturbationData := by
  norm_num [algebraicPerturbationReady, algebraicDegreePositive]
  norm_num [perturbationControlled, sampleAlgebraicPerturbationData]

example : algebraicPerturbationBudget sampleAlgebraicPerturbationData = 13 := by
  native_decide

structure AlgebraicPerturbationBudgetCertificate where
  algebraicDegreeWindow : ℕ
  perturbationBudgetWindow : ℕ
  stabilitySlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AlgebraicPerturbationBudgetCertificate.controlled
    (c : AlgebraicPerturbationBudgetCertificate) : Prop :=
  0 < c.algebraicDegreeWindow ∧
    c.perturbationBudgetWindow ≤
      c.algebraicDegreeWindow + c.stabilitySlackWindow + c.slack

def AlgebraicPerturbationBudgetCertificate.budgetControlled
    (c : AlgebraicPerturbationBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.algebraicDegreeWindow + c.perturbationBudgetWindow + c.stabilitySlackWindow +
      c.slack

def AlgebraicPerturbationBudgetCertificate.Ready
    (c : AlgebraicPerturbationBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AlgebraicPerturbationBudgetCertificate.size
    (c : AlgebraicPerturbationBudgetCertificate) : ℕ :=
  c.algebraicDegreeWindow + c.perturbationBudgetWindow + c.stabilitySlackWindow +
    c.slack

theorem algebraicPerturbation_budgetCertificate_le_size
    (c : AlgebraicPerturbationBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAlgebraicPerturbationBudgetCertificate :
    AlgebraicPerturbationBudgetCertificate :=
  { algebraicDegreeWindow := 4
    perturbationBudgetWindow := 6
    stabilitySlackWindow := 3
    certificateBudgetWindow := 14
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAlgebraicPerturbationBudgetCertificate.Ready := by
  constructor
  · norm_num [AlgebraicPerturbationBudgetCertificate.controlled,
      sampleAlgebraicPerturbationBudgetCertificate]
  · norm_num [AlgebraicPerturbationBudgetCertificate.budgetControlled,
      sampleAlgebraicPerturbationBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAlgebraicPerturbationBudgetCertificate.certificateBudgetWindow ≤
      sampleAlgebraicPerturbationBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAlgebraicPerturbationBudgetCertificate.Ready := by
  constructor
  · norm_num [AlgebraicPerturbationBudgetCertificate.controlled,
      sampleAlgebraicPerturbationBudgetCertificate]
  · norm_num [AlgebraicPerturbationBudgetCertificate.budgetControlled,
      sampleAlgebraicPerturbationBudgetCertificate]

example :
    sampleAlgebraicPerturbationBudgetCertificate.certificateBudgetWindow ≤
      sampleAlgebraicPerturbationBudgetCertificate.size := by
  apply algebraicPerturbation_budgetCertificate_le_size
  constructor
  · norm_num [AlgebraicPerturbationBudgetCertificate.controlled,
      sampleAlgebraicPerturbationBudgetCertificate]
  · norm_num [AlgebraicPerturbationBudgetCertificate.budgetControlled,
      sampleAlgebraicPerturbationBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List AlgebraicPerturbationBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleAlgebraicPerturbationBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleAlgebraicPerturbationBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch7.AlgebraicPerturbationSchemas
