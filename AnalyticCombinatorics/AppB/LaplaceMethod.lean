import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Laplace's method.
-/

namespace AnalyticCombinatorics.AppB.LaplaceMethod

/-- Discrete quadratic phase centered at `center`. -/
def quadraticPhase (center n : ℕ) : ℤ :=
  ((n : ℤ) - (center : ℤ)) ^ 2

/-- Finite check that a phase has its sampled minimum at `center`. -/
def sampledMinimumAt
    (phase : ℕ → ℤ) (center N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => phase center ≤ phase n

/-- Finite check that an amplitude is bounded on a sampled window. -/
def amplitudeBoundedUpTo
    (amplitude : ℕ → ℕ) (bound N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => amplitude n ≤ bound

/-- Finite Laplace-method statement: localized phase plus bounded amplitude. -/
def LaplaceWindow
    (phase : ℕ → ℤ) (amplitude : ℕ → ℕ)
    (center bound N : ℕ) : Prop :=
  sampledMinimumAt phase center N = true ∧
    amplitudeBoundedUpTo amplitude bound N = true

theorem quadraticPhase_sampledMinimum :
    sampledMinimumAt (quadraticPhase 5) 5 12 = true := by
  unfold sampledMinimumAt quadraticPhase
  native_decide

theorem quadraticPhase_laplaceWindow :
    LaplaceWindow (quadraticPhase 5) (fun n => n + 1) 5 13 12 := by
  unfold LaplaceWindow sampledMinimumAt amplitudeBoundedUpTo quadraticPhase
  native_decide

/-- Finite symmetry audit around a quadratic Laplace saddle. -/
def laplaceQuadraticSymmetryCheck (center width : ℕ) : Bool :=
  (List.range (width + 1)).all fun d =>
    quadraticPhase center (center + d) = quadraticPhase center (center - d)

theorem quadraticPhase_laplaceSymmetryWindow :
    laplaceQuadraticSymmetryCheck 6 6 = true := by
  unfold laplaceQuadraticSymmetryCheck quadraticPhase
  native_decide

example : quadraticPhase 5 8 = 9 := by
  unfold quadraticPhase
  native_decide

example : amplitudeBoundedUpTo (fun n => n + 1) 6 5 = true := by
  unfold amplitudeBoundedUpTo
  native_decide

structure LaplaceMethodBudgetCertificate where
  phaseWindow : ℕ
  amplitudeWindow : ℕ
  saddleWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LaplaceMethodBudgetCertificate.controlled
    (c : LaplaceMethodBudgetCertificate) : Prop :=
  0 < c.phaseWindow ∧ c.saddleWindow ≤ c.phaseWindow + c.amplitudeWindow + c.slack

def LaplaceMethodBudgetCertificate.budgetControlled
    (c : LaplaceMethodBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.phaseWindow + c.amplitudeWindow + c.saddleWindow + c.slack

def LaplaceMethodBudgetCertificate.Ready
    (c : LaplaceMethodBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LaplaceMethodBudgetCertificate.size
    (c : LaplaceMethodBudgetCertificate) : ℕ :=
  c.phaseWindow + c.amplitudeWindow + c.saddleWindow + c.slack

theorem laplaceMethod_budgetCertificate_le_size
    (c : LaplaceMethodBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleLaplaceMethodBudgetCertificate :
    LaplaceMethodBudgetCertificate :=
  { phaseWindow := 5
    amplitudeWindow := 6
    saddleWindow := 10
    certificateBudgetWindow := 22
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleLaplaceMethodBudgetCertificate.Ready := by
  constructor
  · norm_num [LaplaceMethodBudgetCertificate.controlled,
      sampleLaplaceMethodBudgetCertificate]
  · norm_num [LaplaceMethodBudgetCertificate.budgetControlled,
      sampleLaplaceMethodBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleLaplaceMethodBudgetCertificate.certificateBudgetWindow ≤
      sampleLaplaceMethodBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleLaplaceMethodBudgetCertificate.Ready := by
  constructor
  · norm_num [LaplaceMethodBudgetCertificate.controlled,
      sampleLaplaceMethodBudgetCertificate]
  · norm_num [LaplaceMethodBudgetCertificate.budgetControlled,
      sampleLaplaceMethodBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List LaplaceMethodBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleLaplaceMethodBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleLaplaceMethodBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.LaplaceMethod
