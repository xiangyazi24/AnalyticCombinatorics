import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Asymptotics: Basic Scales

Executable finite checks for the elementary comparison scales used by
coefficient asymptotics.
-/

namespace AnalyticCombinatorics.Asymptotics.Basic

/-- Finite eventual domination certificate: `a_n <= b_n` for `n0 <= n <= N`. -/
def eventuallyLeUpTo (a b : ℕ → ℕ) (n0 N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => if n < n0 then true else a n ≤ b n

theorem eventuallyLeUpTo_refl (a : ℕ → ℕ) (n0 N : ℕ) :
    eventuallyLeUpTo a a n0 N = true := by
  unfold eventuallyLeUpTo
  simp

theorem linear_le_quadratic_after_one :
    eventuallyLeUpTo (fun n => n) (fun n => n ^ 2) 1 20 = true := by
  native_decide

theorem quadratic_le_exponential_after_four :
    eventuallyLeUpTo (fun n => n ^ 2) (fun n => 2 ^ n) 4 20 = true := by
  native_decide

/-- Rational ratio sample for two natural sequences. -/
def ratioQ (a b : ℕ → ℕ) (n : ℕ) : ℚ :=
  (a n : ℚ) / (b n : ℚ)

theorem ratio_linear_square :
    ratioQ (fun n => n) (fun n => n ^ 2) 1 = 1 ∧
    ratioQ (fun n => n) (fun n => n ^ 2) 2 = 1 / 2 ∧
    ratioQ (fun n => n) (fun n => n ^ 2) 4 = 1 / 4 := by
  native_decide

/-- A finite ratio-decrease check. -/
def ratioNonincreasingUpTo (a b : ℕ → ℕ) (n0 N : ℕ) : Bool :=
  (List.range N).all fun n =>
    if n < n0 then true else ratioQ a b (n + 1) ≤ ratioQ a b n

theorem ratio_n_over_n2_decreases :
    ratioNonincreasingUpTo (fun n => n) (fun n => n ^ 2) 1 20 = true := by
  native_decide

/-- A finite root-growth comparison, expressed without real roots. -/
def rootGrowthBetween (a : ℕ → ℕ) (low high n : ℕ) : Prop :=
  low ^ n < a n ∧ a n < high ^ n

def catalan (n : ℕ) : ℕ :=
  (2 * n).choose n / (n + 1)

theorem catalan_growth_window_10 :
    rootGrowthBetween catalan 2 4 10 := by
  change 2 ^ 10 < catalan 10 ∧ catalan 10 < 4 ^ 10
  native_decide

theorem catalan_growth_window_15 :
    rootGrowthBetween catalan 2 4 15 := by
  change 2 ^ 15 < catalan 15 ∧ catalan 15 < 4 ^ 15
  native_decide

/-- Central binomial coefficients provide the basic `4^n / sqrt(n)` scale. -/
def centralBinom (n : ℕ) : ℕ :=
  (2 * n).choose n

theorem central_binom_exponential_window :
    ∀ n : Fin 10, 1 ≤ n.val → centralBinom n.val < 4 ^ n.val := by
  native_decide

theorem central_binom_lower_window :
    ∀ n : Fin 10, 1 ≤ n.val → 4 ^ n.val ≤ centralBinom n.val * (2 * n.val + 1) := by
  native_decide

/-- Finite ratio window for coefficient-transfer outputs. -/
def ratioWithinQ (a b : ℕ → ℕ) (lower upper : ℚ) (n : ℕ) : Prop :=
  lower ≤ ratioQ a b n ∧ ratioQ a b n ≤ upper

theorem catalan_to_central_ratio_window :
    ∀ n : Fin 9, 1 ≤ n.val →
      ratioWithinQ catalan centralBinom (1 / 10) 1 n.val := by
  unfold ratioWithinQ ratioQ catalan centralBinom
  native_decide

/-- A finite little-oh style certificate: ratios are below a fixed rational tolerance. -/
def ratioBelowAfter (a b : ℕ → ℕ) (eps : ℚ) (n0 N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    if n < n0 then true else ratioQ a b n ≤ eps

theorem n_over_n2_below_tenth_after_ten :
    ratioBelowAfter (fun n => n) (fun n => n ^ 2) (1 / 10) 10 40 = true := by
  native_decide

/-- Finite sampled equivalence certificate. -/
def AsymptoticEquivalent
    (a b : ℕ → ℕ) (N : ℕ) : Prop :=
  ∀ n, n ≤ N → a n = b n

theorem asymptotic_equivalent_refl (a : ℕ → ℕ) (N : ℕ) :
    AsymptoticEquivalent a a N := by
  intro n hn
  rfl

theorem asymptotic_equivalent_symm {a b : ℕ → ℕ} {N : ℕ}
    (h : AsymptoticEquivalent a b N) :
    AsymptoticEquivalent b a N := by
  intro n hn
  exact (h n hn).symm

theorem asymptotic_equivalent_trans {a b c : ℕ → ℕ} {N : ℕ}
    (hab : AsymptoticEquivalent a b N)
    (hbc : AsymptoticEquivalent b c N) :
    AsymptoticEquivalent a c N := by
  intro n hn
  exact (hab n hn).trans (hbc n hn)

structure BasicScaleCertificate where
  startIndex : ℕ
  sampleBound : ℕ
  ratioBudget : ℕ
  growthBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BasicScaleCertificate.sampleControlled
    (c : BasicScaleCertificate) : Prop :=
  c.startIndex ≤ c.sampleBound + c.slack

def BasicScaleCertificate.growthControlled
    (c : BasicScaleCertificate) : Prop :=
  c.growthBudget ≤ c.startIndex + c.sampleBound + c.ratioBudget + c.slack

def basicScaleCertificateReady (c : BasicScaleCertificate) : Prop :=
  0 < c.sampleBound ∧ c.sampleControlled ∧ c.growthControlled

def BasicScaleCertificate.size (c : BasicScaleCertificate) : ℕ :=
  c.startIndex + c.sampleBound + c.ratioBudget + c.slack

theorem basicScale_growthBudget_le_size {c : BasicScaleCertificate}
    (h : basicScaleCertificateReady c) :
    c.growthBudget ≤ c.size := by
  rcases h with ⟨_, _, hgrowth⟩
  exact hgrowth

def sampleBasicScaleCertificate : BasicScaleCertificate :=
  { startIndex := 4, sampleBound := 20, ratioBudget := 5,
    growthBudget := 29, slack := 0 }

example : basicScaleCertificateReady sampleBasicScaleCertificate := by
  norm_num [basicScaleCertificateReady,
    BasicScaleCertificate.sampleControlled,
    BasicScaleCertificate.growthControlled,
    sampleBasicScaleCertificate]

example :
    sampleBasicScaleCertificate.growthBudget ≤
      sampleBasicScaleCertificate.size := by
  norm_num [BasicScaleCertificate.size, sampleBasicScaleCertificate]

/-- Finite executable readiness audit for sampled basic-scale certificates. -/
def basicScaleCertificateListReady
    (certs : List BasicScaleCertificate) : Bool :=
  certs.all fun c =>
    0 < c.sampleBound &&
      c.startIndex ≤ c.sampleBound + c.slack &&
        c.growthBudget ≤ c.startIndex + c.sampleBound + c.ratioBudget + c.slack

theorem basicScaleCertificateList_readyWindow :
    basicScaleCertificateListReady
      [{ startIndex := 1, sampleBound := 10, ratioBudget := 3,
         growthBudget := 14, slack := 0 },
       { startIndex := 4, sampleBound := 20, ratioBudget := 5,
         growthBudget := 29, slack := 0 }] = true := by
  unfold basicScaleCertificateListReady
  native_decide

/-- A refinement certificate for basic sampled scale comparisons. -/
structure BasicScaleRefinementCertificate where
  startIndex : ℕ
  sampleBound : ℕ
  ratioBudget : ℕ
  growthBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BasicScaleRefinementCertificate.sampleControlled
    (cert : BasicScaleRefinementCertificate) : Prop :=
  0 < cert.sampleBound ∧ cert.startIndex ≤ cert.sampleBound + cert.slack

def BasicScaleRefinementCertificate.budgetControlled
    (cert : BasicScaleRefinementCertificate) : Prop :=
  cert.growthBudgetWindow ≤
      cert.startIndex + cert.sampleBound + cert.ratioBudget + cert.slack ∧
    cert.certificateBudgetWindow ≤
      cert.startIndex + cert.sampleBound + cert.ratioBudget +
        cert.growthBudgetWindow + cert.slack

def basicScaleRefinementReady
    (cert : BasicScaleRefinementCertificate) : Prop :=
  cert.sampleControlled ∧ cert.budgetControlled

def BasicScaleRefinementCertificate.size
    (cert : BasicScaleRefinementCertificate) : ℕ :=
  cert.startIndex + cert.sampleBound + cert.ratioBudget +
    cert.growthBudgetWindow + cert.slack

theorem basicScale_certificateBudgetWindow_le_size
    (cert : BasicScaleRefinementCertificate)
    (h : basicScaleRefinementReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleBasicScaleRefinementCertificate :
    BasicScaleRefinementCertificate :=
  { startIndex := 4, sampleBound := 20, ratioBudget := 5,
    growthBudgetWindow := 29, certificateBudgetWindow := 58, slack := 0 }

example : basicScaleRefinementReady sampleBasicScaleRefinementCertificate := by
  norm_num [basicScaleRefinementReady,
    BasicScaleRefinementCertificate.sampleControlled,
    BasicScaleRefinementCertificate.budgetControlled,
    sampleBasicScaleRefinementCertificate]

example :
    sampleBasicScaleRefinementCertificate.certificateBudgetWindow ≤
      sampleBasicScaleRefinementCertificate.size := by
  apply basicScale_certificateBudgetWindow_le_size
  norm_num [basicScaleRefinementReady,
    BasicScaleRefinementCertificate.sampleControlled,
    BasicScaleRefinementCertificate.budgetControlled,
    sampleBasicScaleRefinementCertificate]


structure BasicBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BasicBudgetCertificate.controlled
    (c : BasicBudgetCertificate) : Prop :=
  0 < c.primaryWindow ∧ c.secondaryWindow ≤ c.primaryWindow + c.slack

def BasicBudgetCertificate.budgetControlled
    (c : BasicBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def BasicBudgetCertificate.Ready
    (c : BasicBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BasicBudgetCertificate.size
    (c : BasicBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem basic_budgetCertificate_le_size
    (c : BasicBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleBasicBudgetCertificate :
    BasicBudgetCertificate :=
  { primaryWindow := 5
    secondaryWindow := 6
    certificateBudgetWindow := 12
    slack := 1 }

example : sampleBasicBudgetCertificate.Ready := by
  constructor
  · norm_num [BasicBudgetCertificate.controlled,
      sampleBasicBudgetCertificate]
  · norm_num [BasicBudgetCertificate.budgetControlled,
      sampleBasicBudgetCertificate]

example :
    sampleBasicBudgetCertificate.certificateBudgetWindow ≤
      sampleBasicBudgetCertificate.size := by
  apply basic_budgetCertificate_le_size
  constructor
  · norm_num [BasicBudgetCertificate.controlled,
      sampleBasicBudgetCertificate]
  · norm_num [BasicBudgetCertificate.budgetControlled,
      sampleBasicBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleBasicBudgetCertificate.Ready := by
  constructor
  · norm_num [BasicBudgetCertificate.controlled,
      sampleBasicBudgetCertificate]
  · norm_num [BasicBudgetCertificate.budgetControlled,
      sampleBasicBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleBasicBudgetCertificate.certificateBudgetWindow ≤
      sampleBasicBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List BasicBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleBasicBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleBasicBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.Basic
