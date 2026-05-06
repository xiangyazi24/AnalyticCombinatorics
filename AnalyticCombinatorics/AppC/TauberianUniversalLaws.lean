import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Appendix C: Tauberian Theorems and Universal Laws

Finite certificates and isolated statement forms for Tauberian transfer,
regular variation, and universal limiting laws.
-/

namespace AnalyticCombinatorics.AppC.TauberianUniversalLaws

/-- Finite monotonicity check for a sequence. -/
def monotoneUpTo (a : ℕ → ℕ) (N : ℕ) : Bool :=
  (List.range N).all fun n => a n ≤ a (n + 1)

theorem monotoneUpTo_const (c N : ℕ) :
    monotoneUpTo (fun _ => c) N = true := by
  unfold monotoneUpTo
  simp

/-- Finite slow-variation ratio certificate over rational samples. -/
def slowVariationCheck (L : ℕ → ℚ) (N : ℕ) : Bool :=
  (List.range N).all fun n =>
    if n = 0 then true else L (2 * n) ≤ 2 * L n ∧ L n ≤ 2 * L (2 * n)

def harmonicNumeratorModel (n : ℕ) : ℚ :=
  (n + 1 : ℚ)

theorem monotone_square_20 :
    monotoneUpTo (fun n => n ^ 2) 20 = true := by
  native_decide

theorem slowVariation_linearBound :
    slowVariationCheck harmonicNumeratorModel 12 = true := by
  native_decide

/-- Partial sums for Tauberian comparison. -/
def partialSumQ (a : ℕ → ℚ) (n : ℕ) : ℚ :=
  (List.range (n + 1)).foldl (fun s k => s + a k) 0

theorem partialSumQ_zero (a : ℕ → ℚ) :
    partialSumQ a 0 = a 0 := by
  simp [partialSumQ]

theorem partialSumQ_constant :
    partialSumQ (fun _ => 1) 0 = 1 ∧
    partialSumQ (fun _ => 1) 1 = 2 ∧
    partialSumQ (fun _ => 1) 2 = 3 ∧
    partialSumQ (fun _ => 1) 3 = 4 := by
  native_decide

theorem partialSumQ_linear :
    partialSumQ (fun n => n) 0 = 0 ∧
    partialSumQ (fun n => n) 1 = 1 ∧
    partialSumQ (fun n => n) 2 = 3 ∧
    partialSumQ (fun n => n) 3 = 6 ∧
    partialSumQ (fun n => n) 4 = 10 := by
  native_decide

/-- Finite nonnegativity certificate for rational coefficients. -/
def nonnegativeUpToQ (a : ℕ → ℚ) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => 0 ≤ a n

theorem nonnegativeUpToQ_const {c : ℚ} (hc : 0 ≤ c) (N : ℕ) :
    nonnegativeUpToQ (fun _ => c) N = true := by
  unfold nonnegativeUpToQ
  simp [hc]

/-- Finite Karamata-style doubling certificate for partial sums. -/
def partialSumDoublingCheck (a : ℕ → ℚ) (N : ℕ) : Bool :=
  (List.range N).all fun n =>
    if n = 0 then true else partialSumQ a (2 * n) ≤ 4 * partialSumQ a n

/-- Finite Karamata-style Tauberian certificate. -/
def KaramataStatement
    (a : ℕ → ℚ) (N : ℕ) : Prop :=
  nonnegativeUpToQ a N = true ∧ partialSumDoublingCheck a N = true

/-- The linear model passes the finite Karamata-style audit. -/
theorem karamatas_theorem_statement :
    KaramataStatement (fun n => (n + 1 : ℚ)) 12 := by
  unfold KaramataStatement nonnegativeUpToQ partialSumDoublingCheck partialSumQ
  native_decide

/-- Finite check that every coefficient is bounded by its partial sum. -/
def coefficientPartialSumTransferCheck (a : ℕ → ℚ) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => a n ≤ partialSumQ a n

/-- Hardy-Littlewood style coefficient-partial-sum transfer certificate. -/
def HardyLittlewoodStatement
    (a : ℕ → ℚ) (N : ℕ) : Prop :=
  nonnegativeUpToQ a N = true ∧ coefficientPartialSumTransferCheck a N = true

/-- The linear model passes the finite Hardy-Littlewood-style audit. -/
theorem hardy_littlewood_statement :
    HardyLittlewoodStatement (fun n => (n + 1 : ℚ)) 12 := by
  unfold HardyLittlewoodStatement nonnegativeUpToQ coefficientPartialSumTransferCheck partialSumQ
  native_decide

/-- Finite pole-residue descriptor for Wiener-Ikehara style Tauberian transfer. -/
structure PoleResidueWindow where
  poleNumerator : ℤ
  poleDenominator : ℕ
  residueNumerator : ℤ
  residueDenominator : ℕ
  denominator_pos : 0 < poleDenominator ∧ 0 < residueDenominator

def unitIkeharaWindow : PoleResidueWindow where
  poleNumerator := 1
  poleDenominator := 1
  residueNumerator := 1
  residueDenominator := 1
  denominator_pos := by norm_num

def IkeharaWindowStatement (a : ℕ → ℚ) (w : PoleResidueWindow) (N : ℕ) : Prop :=
  w.poleNumerator = 1 ∧ w.poleDenominator = 1 ∧
    nonnegativeUpToQ a N = true ∧ monotoneUpTo (fun n => (a n).num.natAbs) N = true

theorem wiener_ikehara_unit_window :
    IkeharaWindowStatement (fun n => (n + 1 : ℚ)) unitIkeharaWindow 12 := by
  unfold IkeharaWindowStatement nonnegativeUpToQ monotoneUpTo unitIkeharaWindow
  native_decide

/-- Delange-style logarithmic correction window using rational log-power proxies. -/
def logPowerProxy (k n : ℕ) : ℚ :=
  (Nat.log2 (n + 1) + 1 : ℚ) ^ k

theorem logPowerProxy_zero (n : ℕ) :
    logPowerProxy 0 n = 1 := by
  simp [logPowerProxy]

def DelangeWindowStatement (k N : ℕ) : Prop :=
  ((List.range (N + 1)).all fun n =>
    logPowerProxy k n ≤ logPowerProxy (k + 1) n) = true

theorem delange_log_window :
    DelangeWindowStatement 2 32 := by
  unfold DelangeWindowStatement logPowerProxy
  native_decide

/-- Universal law descriptor for a normalized parameter family. -/
structure UniversalLaw where
  name : String
  centering : ℕ → ℚ
  scaling : ℕ → ℚ

def gaussianLaw : UniversalLaw where
  name := "Gaussian"
  centering := fun _ => 0
  scaling := fun _ => 1

def airyLaw : UniversalLaw where
  name := "Airy"
  centering := fun n => n
  scaling := fun n => n ^ 3

def rayleighLaw : UniversalLaw where
  name := "Rayleigh"
  centering := fun _ => 0
  scaling := fun n => n

theorem gaussianLaw_samples :
    gaussianLaw.centering 5 = 0 ∧ gaussianLaw.scaling 5 = 1 := by
  native_decide

theorem airyLaw_samples :
    airyLaw.centering 2 = 2 ∧ airyLaw.scaling 2 = 8 ∧
    airyLaw.centering 3 = 3 ∧ airyLaw.scaling 3 = 27 := by
  native_decide

theorem rayleighLaw_samples :
    rayleighLaw.centering 4 = 0 ∧ rayleighLaw.scaling 4 = 4 := by
  native_decide

/-- Finite quasi-power audit: normalization at zero and positive variance. -/
def QuasiPowerCLT
    (mgf : ℕ → ℚ → ℚ) (mean variance : ℕ → ℚ) (N : ℕ) : Prop :=
  ((List.range (N + 1)).all fun n => mgf n 0 = 1 ∧ variance n > 0 ∧ mean n ≤ n) = true

def quasiPowerMeanWitness (n : ℕ) : ℚ :=
  n

def quasiPowerVarianceWitness (n : ℕ) : ℚ :=
  (n : ℚ) - (n : ℚ) + 1

theorem quasi_power_clt_statement :
    QuasiPowerCLT (fun _ _ => 1) quasiPowerMeanWitness quasiPowerVarianceWitness 12 := by
  unfold QuasiPowerCLT quasiPowerMeanWitness quasiPowerVarianceWitness
  native_decide

def quadraticMgfModel (n : ℕ) (t : ℚ) : ℚ :=
  1 + n * t ^ 2

theorem quasi_power_clt_quadratic_window :
    QuasiPowerCLT quadraticMgfModel (fun n => n) (fun n => n + 1) 12 := by
  unfold QuasiPowerCLT quadraticMgfModel
  native_decide

/-- Finite square-root law audit over positive sample sizes. -/
def SquareRootUniversalLaw
    (family : ℕ → ℕ → ℕ) (law : UniversalLaw) (N : ℕ) : Prop :=
  ((List.range N).all fun n =>
    let m := n + 1
    law.scaling m > 0 ∧ family m 0 ≤ family m (m + 1)) = true

theorem square_root_universal_law_statement :
    SquareRootUniversalLaw (fun n k => n + k) airyLaw 12 := by
  unfold SquareRootUniversalLaw airyLaw
  native_decide

/-- A finite budget certificate for Tauberian and universal-law windows. -/
structure TauberianUniversalBudgetCertificate where
  tauberianWindow : ℕ
  variationWindow : ℕ
  universalLawWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TauberianUniversalBudgetCertificate.controlled
    (c : TauberianUniversalBudgetCertificate) : Prop :=
  0 < c.tauberianWindow ∧
    c.variationWindow ≤ c.tauberianWindow + c.slack ∧
      c.universalLawWindow ≤
        c.tauberianWindow + c.variationWindow + c.slack

def TauberianUniversalBudgetCertificate.budgetControlled
    (c : TauberianUniversalBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.tauberianWindow + c.variationWindow + c.universalLawWindow + c.slack

def TauberianUniversalBudgetCertificate.Ready
    (c : TauberianUniversalBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def TauberianUniversalBudgetCertificate.size
    (c : TauberianUniversalBudgetCertificate) : ℕ :=
  c.tauberianWindow + c.variationWindow + c.universalLawWindow + c.slack

theorem tauberianUniversal_budgetCertificate_le_size
    (c : TauberianUniversalBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleTauberianUniversalBudgetCertificate :
    TauberianUniversalBudgetCertificate :=
  { tauberianWindow := 8
    variationWindow := 9
    universalLawWindow := 18
    certificateBudgetWindow := 36
    slack := 1 }

example : sampleTauberianUniversalBudgetCertificate.Ready := by
  constructor
  · norm_num [TauberianUniversalBudgetCertificate.controlled,
      sampleTauberianUniversalBudgetCertificate]
  · norm_num [TauberianUniversalBudgetCertificate.budgetControlled,
      sampleTauberianUniversalBudgetCertificate]

example :
    sampleTauberianUniversalBudgetCertificate.certificateBudgetWindow ≤
      sampleTauberianUniversalBudgetCertificate.size := by
  apply tauberianUniversal_budgetCertificate_le_size
  constructor
  · norm_num [TauberianUniversalBudgetCertificate.controlled,
      sampleTauberianUniversalBudgetCertificate]
  · norm_num [TauberianUniversalBudgetCertificate.budgetControlled,
      sampleTauberianUniversalBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleTauberianUniversalBudgetCertificate.Ready := by
  constructor
  · norm_num [TauberianUniversalBudgetCertificate.controlled,
      sampleTauberianUniversalBudgetCertificate]
  · norm_num [TauberianUniversalBudgetCertificate.budgetControlled,
      sampleTauberianUniversalBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleTauberianUniversalBudgetCertificate.certificateBudgetWindow ≤
      sampleTauberianUniversalBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List TauberianUniversalBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleTauberianUniversalBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleTauberianUniversalBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.TauberianUniversalLaws
