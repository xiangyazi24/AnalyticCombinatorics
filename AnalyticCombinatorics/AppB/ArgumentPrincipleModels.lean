import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Discrete bookkeeping models for the argument principle.

The analytic theorem is represented here by its integer balance: winding
number equals zeros minus poles.  This keeps later analytic hypotheses
separate from the algebraic accounting they imply.
-/

namespace AnalyticCombinatorics.AppB.ArgumentPrincipleModels

structure BoundaryCount where
  zeros : ℤ
  poles : ℤ
  winding : ℤ
deriving DecidableEq, Repr

def argumentBalance (c : BoundaryCount) : ℤ :=
  c.zeros - c.poles

def satisfiesArgumentPrinciple (c : BoundaryCount) : Prop :=
  c.winding = argumentBalance c

def regularPerturbation (c : BoundaryCount) (delta : ℤ) : BoundaryCount :=
  { zeros := c.zeros + delta, poles := c.poles, winding := c.winding + delta }

def poleCancellation (c : BoundaryCount) (delta : ℤ) : BoundaryCount :=
  { zeros := c.zeros, poles := c.poles + delta, winding := c.winding - delta }

theorem regularPerturbation_preserves {c : BoundaryCount} {delta : ℤ}
    (h : satisfiesArgumentPrinciple c) :
    satisfiesArgumentPrinciple (regularPerturbation c delta) := by
  dsimp [satisfiesArgumentPrinciple, regularPerturbation, argumentBalance] at *
  omega

theorem poleCancellation_preserves {c : BoundaryCount} {delta : ℤ}
    (h : satisfiesArgumentPrinciple c) :
    satisfiesArgumentPrinciple (poleCancellation c delta) := by
  dsimp [satisfiesArgumentPrinciple, poleCancellation, argumentBalance] at *
  omega

def simpleZeroCount : BoundaryCount :=
  { zeros := 3, poles := 1, winding := 2 }

example : satisfiesArgumentPrinciple simpleZeroCount := by
  norm_num [satisfiesArgumentPrinciple, argumentBalance, simpleZeroCount]

example : (regularPerturbation simpleZeroCount 4).winding = 6 := by
  native_decide

example : satisfiesArgumentPrinciple (poleCancellation simpleZeroCount 1) := by
  norm_num [satisfiesArgumentPrinciple, argumentBalance, poleCancellation, simpleZeroCount]


structure ArgumentPrincipleModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ArgumentPrincipleModelsBudgetCertificate.controlled
    (c : ArgumentPrincipleModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def ArgumentPrincipleModelsBudgetCertificate.budgetControlled
    (c : ArgumentPrincipleModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def ArgumentPrincipleModelsBudgetCertificate.Ready
    (c : ArgumentPrincipleModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ArgumentPrincipleModelsBudgetCertificate.size
    (c : ArgumentPrincipleModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem argumentPrincipleModels_budgetCertificate_le_size
    (c : ArgumentPrincipleModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleArgumentPrincipleModelsBudgetCertificate :
    ArgumentPrincipleModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleArgumentPrincipleModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [ArgumentPrincipleModelsBudgetCertificate.controlled,
      sampleArgumentPrincipleModelsBudgetCertificate]
  · norm_num [ArgumentPrincipleModelsBudgetCertificate.budgetControlled,
      sampleArgumentPrincipleModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleArgumentPrincipleModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleArgumentPrincipleModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleArgumentPrincipleModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [ArgumentPrincipleModelsBudgetCertificate.controlled,
      sampleArgumentPrincipleModelsBudgetCertificate]
  · norm_num [ArgumentPrincipleModelsBudgetCertificate.budgetControlled,
      sampleArgumentPrincipleModelsBudgetCertificate]

example :
    sampleArgumentPrincipleModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleArgumentPrincipleModelsBudgetCertificate.size := by
  apply argumentPrincipleModels_budgetCertificate_le_size
  constructor
  · norm_num [ArgumentPrincipleModelsBudgetCertificate.controlled,
      sampleArgumentPrincipleModelsBudgetCertificate]
  · norm_num [ArgumentPrincipleModelsBudgetCertificate.budgetControlled,
      sampleArgumentPrincipleModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List ArgumentPrincipleModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleArgumentPrincipleModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleArgumentPrincipleModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.ArgumentPrincipleModels
