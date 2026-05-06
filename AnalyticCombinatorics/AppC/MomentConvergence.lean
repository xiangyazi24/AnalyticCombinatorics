import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Appendix C: Moment Convergence

Finite moment tables and statement forms for the method of moments.
-/

namespace AnalyticCombinatorics.AppC.MomentConvergence

/-- Moment table indexed by moment order. -/
structure MomentTable where
  moments : List ℚ

def moment (T : MomentTable) (k : ℕ) : ℚ :=
  T.moments.getD k 0

def standardNormalEvenMoments : MomentTable where
  moments := [1, 0, 1, 0, 3, 0, 15, 0, 105]

def poissonOneMoments : MomentTable where
  moments := [1, 1, 2, 5, 15, 52]

theorem standardNormalEvenMoments_samples :
    moment standardNormalEvenMoments 0 = 1 ∧
    moment standardNormalEvenMoments 2 = 1 ∧
    moment standardNormalEvenMoments 4 = 3 ∧
    moment standardNormalEvenMoments 6 = 15 ∧
    moment standardNormalEvenMoments 8 = 105 := by
  native_decide

theorem poissonOneMoments_samples :
    (List.range 6).map (moment poissonOneMoments) = [1, 1, 2, 5, 15, 52] := by
  native_decide

/-- Compare two moment tables through order `K`. -/
def momentsMatchUpTo (A B : MomentTable) (K : ℕ) : Bool :=
  (List.range (K + 1)).all fun k => A.moments.getD k 0 == B.moments.getD k 0

theorem momentsMatch_refl_normal :
    momentsMatchUpTo standardNormalEvenMoments standardNormalEvenMoments 8 = true := by
  native_decide

theorem momentsMatch_normal_poisson_fails :
    momentsMatchUpTo standardNormalEvenMoments poissonOneMoments 4 = false := by
  native_decide

/-- Hankel positivity finite certificate for moment determinacy. -/
def hankel2Det (T : MomentTable) (i : ℕ) : ℚ :=
  moment T i * moment T (i + 2) - moment T (i + 1) ^ 2

theorem normal_hankel2_samples :
    hankel2Det standardNormalEvenMoments 0 = 1 ∧
    hankel2Det standardNormalEvenMoments 2 = 3 ∧
    hankel2Det standardNormalEvenMoments 4 = 45 := by
  native_decide

/-- Finite method-of-moments certificate by sampled moment-table equality. -/
def MethodOfMoments
    (tables : ℕ → MomentTable) (limit : MomentTable) (N K : ℕ) : Prop :=
  (List.range (N + 1)).all (fun n => momentsMatchUpTo (tables n) limit K) = true

theorem method_of_moments_statement :
    MethodOfMoments (fun _ => standardNormalEvenMoments) standardNormalEvenMoments 6 8 := by
  unfold MethodOfMoments momentsMatchUpTo standardNormalEvenMoments
  native_decide

structure MomentConvergenceWindow where
  sampleWindow : ℕ
  momentWindow : ℕ
  determinacySlack : ℕ
  convergenceBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MomentConvergenceWindow.momentsControlled
    (w : MomentConvergenceWindow) : Prop :=
  w.momentWindow ≤ w.sampleWindow + w.determinacySlack + w.slack

def momentConvergenceWindowReady (w : MomentConvergenceWindow) : Prop :=
  0 < w.sampleWindow ∧ w.momentsControlled ∧
    w.convergenceBudget ≤ w.sampleWindow + w.momentWindow + w.slack

def MomentConvergenceWindow.certificate (w : MomentConvergenceWindow) : ℕ :=
  w.sampleWindow + w.momentWindow + w.determinacySlack + w.convergenceBudget + w.slack

theorem momentConvergence_budget_le_certificate (w : MomentConvergenceWindow) :
    w.convergenceBudget ≤ w.certificate := by
  unfold MomentConvergenceWindow.certificate
  omega

def sampleMomentConvergenceWindow : MomentConvergenceWindow :=
  { sampleWindow := 6, momentWindow := 8, determinacySlack := 2,
    convergenceBudget := 15, slack := 1 }

example : momentConvergenceWindowReady sampleMomentConvergenceWindow := by
  norm_num [momentConvergenceWindowReady, MomentConvergenceWindow.momentsControlled,
    sampleMomentConvergenceWindow]


structure MomentConvergenceBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MomentConvergenceBudgetCertificate.controlled
    (c : MomentConvergenceBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def MomentConvergenceBudgetCertificate.budgetControlled
    (c : MomentConvergenceBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def MomentConvergenceBudgetCertificate.Ready
    (c : MomentConvergenceBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def MomentConvergenceBudgetCertificate.size
    (c : MomentConvergenceBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem momentConvergence_budgetCertificate_le_size
    (c : MomentConvergenceBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleMomentConvergenceBudgetCertificate :
    MomentConvergenceBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleMomentConvergenceBudgetCertificate.Ready := by
  constructor
  · norm_num [MomentConvergenceBudgetCertificate.controlled,
      sampleMomentConvergenceBudgetCertificate]
  · norm_num [MomentConvergenceBudgetCertificate.budgetControlled,
      sampleMomentConvergenceBudgetCertificate]

example :
    sampleMomentConvergenceBudgetCertificate.certificateBudgetWindow ≤
      sampleMomentConvergenceBudgetCertificate.size := by
  apply momentConvergence_budgetCertificate_le_size
  constructor
  · norm_num [MomentConvergenceBudgetCertificate.controlled,
      sampleMomentConvergenceBudgetCertificate]
  · norm_num [MomentConvergenceBudgetCertificate.budgetControlled,
      sampleMomentConvergenceBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleMomentConvergenceBudgetCertificate.Ready := by
  constructor
  · norm_num [MomentConvergenceBudgetCertificate.controlled,
      sampleMomentConvergenceBudgetCertificate]
  · norm_num [MomentConvergenceBudgetCertificate.budgetControlled,
      sampleMomentConvergenceBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleMomentConvergenceBudgetCertificate.certificateBudgetWindow ≤
      sampleMomentConvergenceBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List MomentConvergenceBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleMomentConvergenceBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleMomentConvergenceBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.MomentConvergence
