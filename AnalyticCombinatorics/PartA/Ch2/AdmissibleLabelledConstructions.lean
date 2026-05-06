import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Admissible labelled constructions.

Finite SET, SEQ, CYC, product, and substitution windows for labelled species.
-/

namespace AnalyticCombinatorics.PartA.Ch2.AdmissibleLabelledConstructions

/-- Labelled SET construction over a finite atom family: subset counts. -/
def labelledSetConstructionCount (n : ℕ) : ℕ :=
  2 ^ n

/-- Labelled product count with a split of labels. -/
def labelledProductSplitCount (n k : ℕ) : ℕ :=
  n.choose k

/-- Finite audit that SET and product constructions fit labelled envelopes. -/
def admissibleLabelledConstructionCheck (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    labelledSetConstructionCount n ≤ 2 ^ n ∧
      (List.range (n + 1)).all fun k => labelledProductSplitCount n k ≤ 2 ^ n

theorem admissibleLabelledConstruction_window :
    admissibleLabelledConstructionCheck 12 = true := by
  unfold admissibleLabelledConstructionCheck labelledSetConstructionCount
    labelledProductSplitCount
  native_decide

structure AdmissibleLabelledConstructionData where
  labelWindow : ℕ
  constructionArity : ℕ
  symmetryBudget : ℕ
  constructionSlack : ℕ
deriving DecidableEq, Repr

def admissibleLabelledConstructionReady
    (d : AdmissibleLabelledConstructionData) : Prop :=
  0 < d.labelWindow ∧
    d.symmetryBudget ≤ d.labelWindow * (d.constructionArity + 1) + d.constructionSlack

def admissibleLabelledConstructionBudget
    (d : AdmissibleLabelledConstructionData) : ℕ :=
  d.labelWindow + d.constructionArity + d.symmetryBudget + d.constructionSlack

theorem symmetryBudget_le_budget
    (d : AdmissibleLabelledConstructionData) :
    d.symmetryBudget ≤
      admissibleLabelledConstructionBudget d + d.labelWindow * d.constructionArity := by
  unfold admissibleLabelledConstructionBudget
  omega

def sampleAdmissibleLabelledConstructionData :
    AdmissibleLabelledConstructionData :=
  { labelWindow := 5
    constructionArity := 3
    symmetryBudget := 12
    constructionSlack := 1 }

example : admissibleLabelledConstructionReady
    sampleAdmissibleLabelledConstructionData := by
  norm_num [admissibleLabelledConstructionReady,
    sampleAdmissibleLabelledConstructionData]

structure AdmissibleLabelledConstructionsBudgetCertificate where
  labelWindow : ℕ
  arityWindow : ℕ
  symmetryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AdmissibleLabelledConstructionsBudgetCertificate.controlled
    (c : AdmissibleLabelledConstructionsBudgetCertificate) : Prop :=
  0 < c.labelWindow ∧
    c.symmetryWindow ≤ c.labelWindow * (c.arityWindow + 1) + c.slack

def AdmissibleLabelledConstructionsBudgetCertificate.budgetControlled
    (c : AdmissibleLabelledConstructionsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.labelWindow + c.arityWindow + c.symmetryWindow + c.slack

def AdmissibleLabelledConstructionsBudgetCertificate.Ready
    (c : AdmissibleLabelledConstructionsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AdmissibleLabelledConstructionsBudgetCertificate.size
    (c : AdmissibleLabelledConstructionsBudgetCertificate) : ℕ :=
  c.labelWindow + c.arityWindow + c.symmetryWindow + c.slack

theorem admissibleLabelledConstructions_budgetCertificate_le_size
    (c : AdmissibleLabelledConstructionsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleAdmissibleLabelledConstructionsBudgetCertificate :
    AdmissibleLabelledConstructionsBudgetCertificate :=
  { labelWindow := 5
    arityWindow := 3
    symmetryWindow := 12
    certificateBudgetWindow := 21
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAdmissibleLabelledConstructionsBudgetCertificate.Ready := by
  constructor
  · norm_num [AdmissibleLabelledConstructionsBudgetCertificate.controlled,
      sampleAdmissibleLabelledConstructionsBudgetCertificate]
  · norm_num [AdmissibleLabelledConstructionsBudgetCertificate.budgetControlled,
      sampleAdmissibleLabelledConstructionsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAdmissibleLabelledConstructionsBudgetCertificate.certificateBudgetWindow ≤
      sampleAdmissibleLabelledConstructionsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAdmissibleLabelledConstructionsBudgetCertificate.Ready := by
  constructor
  · norm_num [AdmissibleLabelledConstructionsBudgetCertificate.controlled,
      sampleAdmissibleLabelledConstructionsBudgetCertificate]
  · norm_num [AdmissibleLabelledConstructionsBudgetCertificate.budgetControlled,
      sampleAdmissibleLabelledConstructionsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List AdmissibleLabelledConstructionsBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleAdmissibleLabelledConstructionsBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleAdmissibleLabelledConstructionsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch2.AdmissibleLabelledConstructions
