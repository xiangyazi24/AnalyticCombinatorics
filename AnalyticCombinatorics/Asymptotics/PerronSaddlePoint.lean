import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Perron saddle-point windows.
-/

namespace AnalyticCombinatorics.Asymptotics.PerronSaddlePoint

/-- Finite Dirichlet-prefix sum for Perron-style coefficient extraction. -/
def dirichletPrefixQ (a : ℕ → ℚ) (n : ℕ) : ℚ :=
  (List.range (n + 1)).foldl (fun s k => s + a k / (k + 1 : ℚ)) 0

/-- Finite nonnegativity audit for Perron coefficients. -/
def nonnegativeUpToQ (a : ℕ → ℚ) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => 0 ≤ a n

/-- Finite Perron-window bound against a rational envelope. -/
def perronEnvelopeCheck
    (a envelope : ℕ → ℚ) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => dirichletPrefixQ a n ≤ envelope n

def PerronWindow (a envelope : ℕ → ℚ) (N : ℕ) : Prop :=
  nonnegativeUpToQ a N = true ∧ perronEnvelopeCheck a envelope N = true

theorem unit_perronPrefix_window :
    dirichletPrefixQ (fun _ => 1) 0 = 1 ∧
    dirichletPrefixQ (fun _ => 1) 1 = 3 / 2 ∧
    dirichletPrefixQ (fun _ => 1) 2 = 11 / 6 := by
  unfold dirichletPrefixQ
  native_decide

theorem unit_perronWindow :
    PerronWindow (fun _ => 1) (fun n => (n + 1 : ℚ)) 16 := by
  unfold PerronWindow nonnegativeUpToQ perronEnvelopeCheck dirichletPrefixQ
  native_decide

/-- Finite monotonicity audit for nonnegative Perron prefixes. -/
def perronPrefixMonotoneCheck (a : ℕ → ℚ) (N : ℕ) : Bool :=
  (List.range N).all fun n => dirichletPrefixQ a n ≤ dirichletPrefixQ a (n + 1)

theorem unit_perronPrefix_monotoneWindow :
    perronPrefixMonotoneCheck (fun _ => 1) 16 = true := by
  unfold perronPrefixMonotoneCheck dirichletPrefixQ
  native_decide

example : dirichletPrefixQ (fun _ => 1) 3 = 25 / 12 := by
  unfold dirichletPrefixQ
  native_decide

example : perronPrefixMonotoneCheck (fun _ => 1) 6 = true := by
  unfold perronPrefixMonotoneCheck dirichletPrefixQ
  native_decide

structure PerronSaddlePointBudgetCertificate where
  perronWindow : ℕ
  saddleWindow : ℕ
  residueWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PerronSaddlePointBudgetCertificate.controlled
    (c : PerronSaddlePointBudgetCertificate) : Prop :=
  0 < c.perronWindow ∧
    c.residueWindow ≤ c.perronWindow + c.saddleWindow + c.slack

def PerronSaddlePointBudgetCertificate.budgetControlled
    (c : PerronSaddlePointBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.perronWindow + c.saddleWindow + c.residueWindow + c.slack

def PerronSaddlePointBudgetCertificate.Ready
    (c : PerronSaddlePointBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PerronSaddlePointBudgetCertificate.size
    (c : PerronSaddlePointBudgetCertificate) : ℕ :=
  c.perronWindow + c.saddleWindow + c.residueWindow + c.slack

theorem perronSaddlePoint_budgetCertificate_le_size
    (c : PerronSaddlePointBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def samplePerronSaddlePointBudgetCertificate :
    PerronSaddlePointBudgetCertificate :=
  { perronWindow := 5
    saddleWindow := 6
    residueWindow := 10
    certificateBudgetWindow := 22
    slack := 1 }

example : samplePerronSaddlePointBudgetCertificate.Ready := by
  constructor
  · norm_num [PerronSaddlePointBudgetCertificate.controlled,
      samplePerronSaddlePointBudgetCertificate]
  · norm_num [PerronSaddlePointBudgetCertificate.budgetControlled,
      samplePerronSaddlePointBudgetCertificate]

/-- Finite executable readiness audit for Perron saddle-point certificates. -/
def perronSaddlePointCertificateListReady
    (certs : List PerronSaddlePointBudgetCertificate) : Bool :=
  certs.all fun c =>
    0 < c.perronWindow &&
      c.residueWindow ≤ c.perronWindow + c.saddleWindow + c.slack &&
        c.certificateBudgetWindow ≤
          c.perronWindow + c.saddleWindow + c.residueWindow + c.slack

theorem perronSaddlePointCertificateList_readyWindow :
    perronSaddlePointCertificateListReady
      [{ perronWindow := 3, saddleWindow := 4, residueWindow := 6,
         certificateBudgetWindow := 13, slack := 0 },
       { perronWindow := 5, saddleWindow := 6, residueWindow := 10,
         certificateBudgetWindow := 22, slack := 1 }] = true := by
  unfold perronSaddlePointCertificateListReady
  native_decide

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    samplePerronSaddlePointBudgetCertificate.Ready := by
  constructor
  · norm_num [PerronSaddlePointBudgetCertificate.controlled,
      samplePerronSaddlePointBudgetCertificate]
  · norm_num [PerronSaddlePointBudgetCertificate.budgetControlled,
      samplePerronSaddlePointBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    samplePerronSaddlePointBudgetCertificate.certificateBudgetWindow ≤
      samplePerronSaddlePointBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List PerronSaddlePointBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [samplePerronSaddlePointBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    samplePerronSaddlePointBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.PerronSaddlePoint
