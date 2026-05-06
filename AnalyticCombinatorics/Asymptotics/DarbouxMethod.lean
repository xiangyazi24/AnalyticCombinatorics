import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Darboux method
-/

namespace AnalyticCombinatorics.Asymptotics.DarbouxMethod

/-- Coefficient model for a finite local expansion at a dominant point. -/
def localExpansionCoeff (coeff : ℕ → ℤ) (order n : ℕ) : ℤ :=
  if n < order then coeff n else 0

theorem localExpansionCoeff_of_lt
    {coeff : ℕ → ℤ} {order n : ℕ} (h : n < order) :
    localExpansionCoeff coeff order n = coeff n := by
  simp [localExpansionCoeff, h]

theorem localExpansionCoeff_of_not_lt
    {coeff : ℕ → ℤ} {order n : ℕ} (h : ¬ n < order) :
    localExpansionCoeff coeff order n = 0 := by
  simp [localExpansionCoeff, h]

/-- Prefix agreement of an approximation with a finite local expansion. -/
def agreesWithLocalExpansion
    (coeff approx : ℕ → ℤ) (order : ℕ) : Prop :=
  ∀ n, n < order → approx n = coeff n

theorem localExpansionCoeff_agrees
    (coeff : ℕ → ℤ) (order : ℕ) :
    agreesWithLocalExpansion coeff (localExpansionCoeff coeff order) order := by
  intro n hn
  exact localExpansionCoeff_of_lt hn

structure DarbouxWindow where
  localWindow : ℕ
  coefficientWindow : ℕ
  remainderWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DarbouxWindow.ready (w : DarbouxWindow) : Prop :=
  0 < w.localWindow ∧
    w.remainderWindow ≤ w.localWindow + w.coefficientWindow + w.slack

def sampleDarbouxWindow : DarbouxWindow :=
  { localWindow := 4, coefficientWindow := 3,
    remainderWindow := 7, slack := 0 }

example : sampleDarbouxWindow.ready := by
  norm_num [DarbouxWindow.ready, sampleDarbouxWindow]

structure BudgetCertificate where
  localWindow : ℕ
  coefficientWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.localWindow ∧ c.coefficientWindow ≤ c.localWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.localWindow + c.coefficientWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.localWindow + c.coefficientWindow + c.slack

theorem darbouxMethod_budgetCertificate_le_size
    (c : BudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleBudgetCertificate : BudgetCertificate :=
  { localWindow := 5, coefficientWindow := 6,
    certificateBudgetWindow := 12, slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled, sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled, sampleBudgetCertificate]

example : sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled, sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled, sampleBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleBudgetCertificate.certificateBudgetWindow ≤
      sampleBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List BudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleBudgetCertificate
  native_decide

end AnalyticCombinatorics.Asymptotics.DarbouxMethod
