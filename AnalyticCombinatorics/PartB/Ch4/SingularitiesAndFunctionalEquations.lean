import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Singularities and functional equations

Finite discriminant, branch, and implicit-equation windows for singularities
arising from functional equations.
-/

namespace AnalyticCombinatorics.PartB.Ch4.SingularitiesAndFunctionalEquations

def quadraticDiscriminant (a b c : ℤ) : ℤ :=
  b ^ 2 - 4 * a * c

theorem quadraticDiscriminant_samples :
    quadraticDiscriminant 1 2 1 = 0 ∧
      quadraticDiscriminant 1 0 (-1) = 4 := by
  native_decide

theorem quadraticDiscriminant_monic_double_root (r : ℤ) :
    quadraticDiscriminant 1 (-2 * r) (r ^ 2) = 0 := by
  unfold quadraticDiscriminant
  ring

/-- Finite iteration of a functional equation `y = phi(y)`. -/
def functionalIterate (phi : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, seed => seed
  | n + 1, seed => phi (functionalIterate phi n seed)

theorem functionalIterate_zero (phi : ℕ → ℕ) (seed : ℕ) :
    functionalIterate phi 0 seed = seed := rfl

theorem functionalIterate_succ (phi : ℕ → ℕ) (n seed : ℕ) :
    functionalIterate phi (n + 1) seed =
      phi (functionalIterate phi n seed) := rfl

theorem functionalIterate_add_one_sample :
    functionalIterate (fun n => n + 1) 4 0 = 4 := by
  native_decide

structure FunctionalEquationSingularityWindow where
  equationWindow : ℕ
  branchWindow : ℕ
  discriminantWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FunctionalEquationSingularityWindow.ready
    (w : FunctionalEquationSingularityWindow) : Prop :=
  0 < w.equationWindow ∧
    w.branchWindow ≤ w.equationWindow + w.discriminantWindow + w.slack

def sampleFunctionalEquationSingularityWindow :
    FunctionalEquationSingularityWindow :=
  { equationWindow := 5
    branchWindow := 7
    discriminantWindow := 2
    slack := 0 }

example : sampleFunctionalEquationSingularityWindow.ready := by
  norm_num [FunctionalEquationSingularityWindow.ready,
    sampleFunctionalEquationSingularityWindow]

def functionalEquationSingularityWindowListReady
    (data : List FunctionalEquationSingularityWindow) : Bool :=
  data.all fun w =>
    0 < w.equationWindow &&
      w.branchWindow ≤ w.equationWindow + w.discriminantWindow + w.slack

theorem functionalEquationSingularityWindowList_readyWindow :
    functionalEquationSingularityWindowListReady
      [sampleFunctionalEquationSingularityWindow,
       { equationWindow := 3, branchWindow := 4,
         discriminantWindow := 1, slack := 0 }] = true := by
  unfold functionalEquationSingularityWindowListReady
    sampleFunctionalEquationSingularityWindow
  native_decide

structure SingularitiesAndFunctionalEquationsBudgetCertificate where
  equationWindow : ℕ
  branchWindow : ℕ
  singularityWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SingularitiesAndFunctionalEquationsBudgetCertificate.controlled
    (c : SingularitiesAndFunctionalEquationsBudgetCertificate) : Prop :=
  0 < c.equationWindow ∧
    c.branchWindow ≤ c.equationWindow + c.singularityWindow + c.slack

def SingularitiesAndFunctionalEquationsBudgetCertificate.budgetControlled
    (c : SingularitiesAndFunctionalEquationsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.equationWindow + c.branchWindow + c.singularityWindow + c.slack

def SingularitiesAndFunctionalEquationsBudgetCertificate.Ready
    (c : SingularitiesAndFunctionalEquationsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SingularitiesAndFunctionalEquationsBudgetCertificate.size
    (c : SingularitiesAndFunctionalEquationsBudgetCertificate) : ℕ :=
  c.equationWindow + c.branchWindow + c.singularityWindow + c.slack

theorem singularitiesAndFunctionalEquations_budgetCertificate_le_size
    (c : SingularitiesAndFunctionalEquationsBudgetCertificate)
    (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleSingularitiesAndFunctionalEquationsBudgetCertificate :
    SingularitiesAndFunctionalEquationsBudgetCertificate :=
  { equationWindow := 5
    branchWindow := 7
    singularityWindow := 2
    certificateBudgetWindow := 15
    slack := 1 }

example : sampleSingularitiesAndFunctionalEquationsBudgetCertificate.Ready := by
  constructor
  · norm_num [SingularitiesAndFunctionalEquationsBudgetCertificate.controlled,
      sampleSingularitiesAndFunctionalEquationsBudgetCertificate]
  · norm_num
      [SingularitiesAndFunctionalEquationsBudgetCertificate.budgetControlled,
        sampleSingularitiesAndFunctionalEquationsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleSingularitiesAndFunctionalEquationsBudgetCertificate.Ready := by
  constructor
  · norm_num [SingularitiesAndFunctionalEquationsBudgetCertificate.controlled,
      sampleSingularitiesAndFunctionalEquationsBudgetCertificate]
  · norm_num [SingularitiesAndFunctionalEquationsBudgetCertificate.budgetControlled,
      sampleSingularitiesAndFunctionalEquationsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSingularitiesAndFunctionalEquationsBudgetCertificate.certificateBudgetWindow ≤
      sampleSingularitiesAndFunctionalEquationsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List SingularitiesAndFunctionalEquationsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSingularitiesAndFunctionalEquationsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleSingularitiesAndFunctionalEquationsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch4.SingularitiesAndFunctionalEquations
