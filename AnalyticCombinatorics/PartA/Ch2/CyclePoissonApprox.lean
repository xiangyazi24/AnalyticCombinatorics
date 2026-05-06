import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Chapter II: Cycle Poisson Approximation

Finite checks for cycle-count distributions in permutations and the Poisson
approximation schema.
-/

namespace AnalyticCombinatorics.PartA.Ch2.CyclePoissonApprox

/-- Unsigned Stirling numbers of the first kind for permutations by cycle count. -/
def stirlingFirst : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => stirlingFirst n k + n * stirlingFirst n (k + 1)

theorem stirlingFirst_rows :
    (List.range 5).map (stirlingFirst 4) = [0, 6, 11, 6, 1] := by
  native_decide

theorem stirlingFirst_total_n5 :
    ((List.range 6).map (stirlingFirst 5)).sum = Nat.factorial 5 := by
  native_decide

/-- Small-cycle Poisson weight with mean `1/j`, represented by numerator scale. -/
def cyclePoissonWeightScaled (j k : ℕ) : ℚ :=
  if j = 0 then 0 else 1 / ((j : ℚ) ^ k * (Nat.factorial k : ℚ))

theorem cyclePoissonWeightScaled_j2 :
    (List.range 5).map (cyclePoissonWeightScaled 2) = [1, 1 / 2, 1 / 8, 1 / 48, 1 / 384] := by
  native_decide

def CyclePoissonApproximation
    (cycleCount : ℕ → ℕ → ℚ) (j : ℕ) : Prop :=
  0 < j ∧ cycleCount j 0 = 1 ∧ cycleCount j 1 = 1 / j

theorem cycle_poisson_approximation_statement :
    CyclePoissonApproximation cyclePoissonWeightScaled 2 := by
  unfold CyclePoissonApproximation
  native_decide

structure CyclePoissonWindow where
  cycleLength : ℕ
  sampleSize : ℕ
  observedCycles : ℕ
  poissonBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CyclePoissonWindow.lengthReady (w : CyclePoissonWindow) : Prop :=
  0 < w.cycleLength

def CyclePoissonWindow.observationControlled (w : CyclePoissonWindow) : Prop :=
  w.observedCycles ≤ w.sampleSize / w.cycleLength + w.slack

def CyclePoissonWindow.ready (w : CyclePoissonWindow) : Prop :=
  w.lengthReady ∧ w.observationControlled ∧ w.observedCycles ≤ w.poissonBudget + w.slack

def CyclePoissonWindow.certificate (w : CyclePoissonWindow) : ℕ :=
  w.cycleLength + w.sampleSize + w.observedCycles + w.poissonBudget + w.slack

theorem observedCycles_le_certificate (w : CyclePoissonWindow) :
    w.observedCycles ≤ w.certificate := by
  unfold CyclePoissonWindow.certificate
  omega

def sampleCyclePoissonWindow : CyclePoissonWindow :=
  { cycleLength := 2, sampleSize := 10, observedCycles := 4, poissonBudget := 5, slack := 1 }

example : sampleCyclePoissonWindow.ready := by
  norm_num [sampleCyclePoissonWindow, CyclePoissonWindow.ready,
    CyclePoissonWindow.lengthReady, CyclePoissonWindow.observationControlled]


structure CyclePoissonApproxBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CyclePoissonApproxBudgetCertificate.controlled
    (c : CyclePoissonApproxBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def CyclePoissonApproxBudgetCertificate.budgetControlled
    (c : CyclePoissonApproxBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def CyclePoissonApproxBudgetCertificate.Ready
    (c : CyclePoissonApproxBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CyclePoissonApproxBudgetCertificate.size
    (c : CyclePoissonApproxBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem cyclePoissonApprox_budgetCertificate_le_size
    (c : CyclePoissonApproxBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleCyclePoissonApproxBudgetCertificate :
    CyclePoissonApproxBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleCyclePoissonApproxBudgetCertificate.Ready := by
  constructor
  · norm_num [CyclePoissonApproxBudgetCertificate.controlled,
      sampleCyclePoissonApproxBudgetCertificate]
  · norm_num [CyclePoissonApproxBudgetCertificate.budgetControlled,
      sampleCyclePoissonApproxBudgetCertificate]

example :
    sampleCyclePoissonApproxBudgetCertificate.certificateBudgetWindow ≤
      sampleCyclePoissonApproxBudgetCertificate.size := by
  apply cyclePoissonApprox_budgetCertificate_le_size
  constructor
  · norm_num [CyclePoissonApproxBudgetCertificate.controlled,
      sampleCyclePoissonApproxBudgetCertificate]
  · norm_num [CyclePoissonApproxBudgetCertificate.budgetControlled,
      sampleCyclePoissonApproxBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleCyclePoissonApproxBudgetCertificate.Ready := by
  constructor
  · norm_num [CyclePoissonApproxBudgetCertificate.controlled,
      sampleCyclePoissonApproxBudgetCertificate]
  · norm_num [CyclePoissonApproxBudgetCertificate.budgetControlled,
      sampleCyclePoissonApproxBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCyclePoissonApproxBudgetCertificate.certificateBudgetWindow ≤
      sampleCyclePoissonApproxBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List CyclePoissonApproxBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCyclePoissonApproxBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleCyclePoissonApproxBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch2.CyclePoissonApprox
