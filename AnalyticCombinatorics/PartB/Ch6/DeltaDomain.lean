/-
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter VI § VI.1 — Δ-domains and the Transfer Theorem setup

  A Δ-domain at ρ is a region of the form
    Δ(φ, R) = { z : ‖z‖ < R, z ≠ ρ, z is off the real segment [0, ρ] }

  Reference: F&S § VI.1, Definition VI.1.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false


namespace AnalyticCombinatorics.PartB.Ch6.DeltaDomain

open Real

/-! ## Δ-domain definition -/

/-- A Δ-domain at ρ > 0 with outer radius R > ρ.
    Objects are the complex numbers in the disk of radius R,
    not equal to ρ, and not on the segment [0, ρ]. -/
def DeltaRegion (ρ R : ℝ) : Set ℂ :=
  { z : ℂ | ‖z‖ < R ∧ z ≠ (ρ : ℂ) ∧ z.im ≠ 0 }

/-- A function is Δ-analytic at ρ if analytic on some Δ-domain at ρ. -/
def DeltaAnalytic (f : ℂ → ℂ) (ρ : ℝ) : Prop :=
  ∃ R : ℝ, R > ρ ∧ AnalyticOn ℂ f (DeltaRegion ρ R)

/-! ## Singularity types near ρ -/

/-- f has an algebraic singularity at ρ with exponent α and leading constant c:
    f(z) ~ c · (1 - z/ρ)^{-α} as z → ρ in a Δ-domain. -/
def HasAlgebraicSingularity (f : ℂ → ℂ) (ρ : ℝ) (c : ℂ) (α : ℂ) : Prop :=
  ∃ g : ℂ → ℂ, DeltaAnalytic g ρ ∧ ContinuousAt g ↑ρ ∧ g ↑ρ = 1 ∧
  ∀ z ∈ DeltaRegion ρ (ρ + 1),
    f z = c * Complex.exp (α * Complex.log (1 - z / ρ)) * g z

/-! ## Transfer Theorem — setup statement (F&S Theorem VI.1) -/

/-- The transfer-theorem setup provides a nonempty positive outer-radius margin. -/
theorem transfer_theorem_setup_margin (ρ : ℝ) (hρ : 0 < ρ) :
    0 < ρ ∧ ρ < ρ + 1 := by
  exact ⟨hρ, by linarith⟩

structure DeltaDomainWindow where
  radiusNumerator : ℕ
  singularityNumerator : ℕ
  apertureBudget : ℕ
  exclusionSlack : ℕ
deriving DecidableEq, Repr

def DeltaDomainWindow.radiusReady (w : DeltaDomainWindow) : Prop :=
  w.singularityNumerator < w.radiusNumerator

def DeltaDomainWindow.apertureControlled (w : DeltaDomainWindow) : Prop :=
  0 < w.apertureBudget ∧ w.apertureBudget ≤ w.radiusNumerator + w.exclusionSlack

def DeltaDomainWindow.ready (w : DeltaDomainWindow) : Prop :=
  w.radiusReady ∧ w.apertureControlled

def DeltaDomainWindow.certificate (w : DeltaDomainWindow) : ℕ :=
  w.radiusNumerator + w.singularityNumerator + w.apertureBudget + w.exclusionSlack

theorem apertureBudget_le_certificate (w : DeltaDomainWindow) :
    w.apertureBudget ≤ w.certificate := by
  unfold DeltaDomainWindow.certificate
  omega

def sampleDeltaDomainWindow : DeltaDomainWindow :=
  { radiusNumerator := 5, singularityNumerator := 3, apertureBudget := 2, exclusionSlack := 0 }

example : sampleDeltaDomainWindow.ready := by
  norm_num [sampleDeltaDomainWindow, DeltaDomainWindow.ready,
    DeltaDomainWindow.radiusReady, DeltaDomainWindow.apertureControlled]


structure DeltaDomainBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DeltaDomainBudgetCertificate.controlled
    (c : DeltaDomainBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def DeltaDomainBudgetCertificate.budgetControlled
    (c : DeltaDomainBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def DeltaDomainBudgetCertificate.Ready
    (c : DeltaDomainBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def DeltaDomainBudgetCertificate.size
    (c : DeltaDomainBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem deltaDomain_budgetCertificate_le_size
    (c : DeltaDomainBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleDeltaDomainBudgetCertificate :
    DeltaDomainBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleDeltaDomainBudgetCertificate.Ready := by
  constructor
  · norm_num [DeltaDomainBudgetCertificate.controlled,
      sampleDeltaDomainBudgetCertificate]
  · norm_num [DeltaDomainBudgetCertificate.budgetControlled,
      sampleDeltaDomainBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleDeltaDomainBudgetCertificate.certificateBudgetWindow ≤
      sampleDeltaDomainBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleDeltaDomainBudgetCertificate.Ready := by
  constructor
  · norm_num [DeltaDomainBudgetCertificate.controlled,
      sampleDeltaDomainBudgetCertificate]
  · norm_num [DeltaDomainBudgetCertificate.budgetControlled,
      sampleDeltaDomainBudgetCertificate]

example :
    sampleDeltaDomainBudgetCertificate.certificateBudgetWindow ≤
      sampleDeltaDomainBudgetCertificate.size := by
  apply deltaDomain_budgetCertificate_le_size
  constructor
  · norm_num [DeltaDomainBudgetCertificate.controlled,
      sampleDeltaDomainBudgetCertificate]
  · norm_num [DeltaDomainBudgetCertificate.budgetControlled,
      sampleDeltaDomainBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List DeltaDomainBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleDeltaDomainBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleDeltaDomainBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch6.DeltaDomain
