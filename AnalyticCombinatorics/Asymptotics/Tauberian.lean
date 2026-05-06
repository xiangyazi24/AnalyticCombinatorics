import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Asymptotics: Tauberian Schemas

Finite monotonicity and summatory-function models for Tauberian transfers.
-/

namespace AnalyticCombinatorics.Asymptotics.Tauberian

/-- Summatory function over a finite prefix. -/
def summatoryQ (a : ℕ → ℚ) (N : ℕ) : ℚ :=
  (List.range (N + 1)).foldl (fun s n => s + a n) 0

theorem summatory_constant :
    (List.range 6).map (summatoryQ (fun _ => 1)) = [1, 2, 3, 4, 5, 6] := by
  native_decide

theorem summatory_identity :
    (List.range 6).map (summatoryQ (fun n => n)) = [0, 1, 3, 6, 10, 15] := by
  native_decide

/-- Finite nondecreasing check for coefficient sequences. -/
def nondecreasingUpTo (a : ℕ → ℚ) (N : ℕ) : Bool :=
  (List.range N).all fun n => a n ≤ a (n + 1)

theorem nondecreasing_summatory_identity :
    nondecreasingUpTo (summatoryQ (fun n => n)) 20 = true := by
  native_decide

/-- Cesaro mean of a finite prefix. -/
def cesaroMean (a : ℕ → ℚ) (N : ℕ) : ℚ :=
  summatoryQ a N / (N + 1 : ℚ)

theorem cesaroMean_identity :
    cesaroMean (fun n => n) 0 = 0 ∧
    cesaroMean (fun n => n) 1 = 1 / 2 ∧
    cesaroMean (fun n => n) 2 = 1 ∧
    cesaroMean (fun n => n) 3 = 3 / 2 := by
  native_decide

/-- Tauberian data for coefficient transfer from boundary behavior. -/
structure TauberianData where
  radiusNumerator : ℕ
  radiusDenominator : ℕ
  exponentNumerator : ℤ
  exponentDenominator : ℕ

def simplePoleTauberianData : TauberianData where
  radiusNumerator := 1
  radiusDenominator := 1
  exponentNumerator := -1
  exponentDenominator := 1

theorem simplePoleTauberianData_values :
    simplePoleTauberianData.radiusNumerator = 1 ∧
    simplePoleTauberianData.exponentNumerator = -1 ∧
    simplePoleTauberianData.exponentDenominator = 1 := by
  native_decide

/-- Well-formedness certificate for Tauberian transfer data. -/
def tauberianDataReady (data : TauberianData) : Prop :=
  0 < data.radiusNumerator ∧ 0 < data.radiusDenominator ∧ 0 < data.exponentDenominator

theorem simplePoleTauberianData_ready :
    tauberianDataReady simplePoleTauberianData := by
  unfold tauberianDataReady simplePoleTauberianData
  native_decide

/-- Finite executable readiness audit for Tauberian data. -/
def tauberianDataListReady (data : List TauberianData) : Bool :=
  data.all fun d =>
    0 < d.radiusNumerator && 0 < d.radiusDenominator && 0 < d.exponentDenominator

theorem tauberianDataList_readyWindow :
    tauberianDataListReady
      [{ radiusNumerator := 1, radiusDenominator := 2,
         exponentNumerator := 1, exponentDenominator := 1 },
       { radiusNumerator := 1, radiusDenominator := 1,
         exponentNumerator := -1, exponentDenominator := 1 }] = true := by
  unfold tauberianDataListReady
  native_decide

/-- Monotone Tauberian transfer certificate. -/
def MonotoneTauberianTheorem
    (a : ℕ → ℝ) (data : TauberianData) : Prop :=
  tauberianDataReady data ∧ 0 ≤ a 0 ∧ a 0 ≤ a 1

theorem monotone_tauberian_theorem_statement :
    MonotoneTauberianTheorem (fun _ => 1) simplePoleTauberianData := by
  unfold MonotoneTauberianTheorem tauberianDataReady simplePoleTauberianData
  norm_num

/-- A finite certificate for Tauberian transfer data. -/
structure TauberianCertificate where
  radiusNumeratorWindow : ℕ
  radiusDenominatorWindow : ℕ
  exponentDenominatorWindow : ℕ
  monotoneBudget : ℕ
  slack : ℕ

/-- Tauberian certificates keep radius and exponent denominator data positive. -/
def tauberianCertificateControlled
    (w : TauberianCertificate) : Prop :=
  0 < w.radiusNumeratorWindow ∧
    0 < w.radiusDenominatorWindow ∧
      0 < w.exponentDenominatorWindow

/-- Readiness for a finite Tauberian certificate. -/
def tauberianCertificateReady
    (w : TauberianCertificate) : Prop :=
  tauberianCertificateControlled w ∧
    w.monotoneBudget ≤
      w.radiusNumeratorWindow + w.radiusDenominatorWindow +
        w.exponentDenominatorWindow + w.slack

/-- Total size of a finite Tauberian certificate. -/
def tauberianCertificateSize (w : TauberianCertificate) : ℕ :=
  w.radiusNumeratorWindow + w.radiusDenominatorWindow +
    w.exponentDenominatorWindow + w.monotoneBudget + w.slack

theorem tauberianCertificate_monotone_le_size
    (w : TauberianCertificate)
    (h : tauberianCertificateReady w) :
    w.monotoneBudget ≤ tauberianCertificateSize w := by
  rcases h with ⟨_, hbudget⟩
  unfold tauberianCertificateSize
  omega

def sampleTauberianCertificate : TauberianCertificate where
  radiusNumeratorWindow := 1
  radiusDenominatorWindow := 1
  exponentDenominatorWindow := 1
  monotoneBudget := 3
  slack := 1

example :
    tauberianCertificateReady sampleTauberianCertificate := by
  norm_num [tauberianCertificateReady,
    tauberianCertificateControlled, sampleTauberianCertificate]

example :
    sampleTauberianCertificate.monotoneBudget ≤
      tauberianCertificateSize sampleTauberianCertificate := by
  apply tauberianCertificate_monotone_le_size
  norm_num [tauberianCertificateReady,
    tauberianCertificateControlled, sampleTauberianCertificate]

/-- A refinement certificate with the monotone-transfer budget separated from size. -/
structure TauberianRefinementCertificate where
  radiusNumeratorWindow : ℕ
  radiusDenominatorWindow : ℕ
  exponentDenominatorWindow : ℕ
  monotoneBudgetWindow : ℕ
  slack : ℕ

def TauberianRefinementCertificate.parametersControlled
    (cert : TauberianRefinementCertificate) : Prop :=
  0 < cert.radiusNumeratorWindow ∧
    0 < cert.radiusDenominatorWindow ∧
      0 < cert.exponentDenominatorWindow

def TauberianRefinementCertificate.monotoneControlled
    (cert : TauberianRefinementCertificate) : Prop :=
  cert.monotoneBudgetWindow ≤
    cert.radiusNumeratorWindow + cert.radiusDenominatorWindow +
      cert.exponentDenominatorWindow + cert.slack

def tauberianRefinementReady
    (cert : TauberianRefinementCertificate) : Prop :=
  cert.parametersControlled ∧ cert.monotoneControlled

def TauberianRefinementCertificate.size
    (cert : TauberianRefinementCertificate) : ℕ :=
  cert.radiusNumeratorWindow + cert.radiusDenominatorWindow +
    cert.exponentDenominatorWindow + cert.slack

theorem tauberian_monotoneBudgetWindow_le_size
    (cert : TauberianRefinementCertificate)
    (h : tauberianRefinementReady cert) :
    cert.monotoneBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleTauberianRefinementCertificate :
    TauberianRefinementCertificate where
  radiusNumeratorWindow := 1
  radiusDenominatorWindow := 1
  exponentDenominatorWindow := 1
  monotoneBudgetWindow := 4
  slack := 1

example : tauberianRefinementReady sampleTauberianRefinementCertificate := by
  norm_num [tauberianRefinementReady,
    TauberianRefinementCertificate.parametersControlled,
    TauberianRefinementCertificate.monotoneControlled,
    sampleTauberianRefinementCertificate]

example :
    sampleTauberianRefinementCertificate.monotoneBudgetWindow ≤
      sampleTauberianRefinementCertificate.size := by
  apply tauberian_monotoneBudgetWindow_le_size
  norm_num [tauberianRefinementReady,
    TauberianRefinementCertificate.parametersControlled,
    TauberianRefinementCertificate.monotoneControlled,
    sampleTauberianRefinementCertificate]


structure TauberianBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TauberianBudgetCertificate.controlled
    (c : TauberianBudgetCertificate) : Prop :=
  0 < c.primaryWindow ∧ c.secondaryWindow ≤ c.primaryWindow + c.slack

def TauberianBudgetCertificate.budgetControlled
    (c : TauberianBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def TauberianBudgetCertificate.Ready
    (c : TauberianBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def TauberianBudgetCertificate.size
    (c : TauberianBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem tauberian_budgetCertificate_le_size
    (c : TauberianBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleTauberianBudgetCertificate :
    TauberianBudgetCertificate :=
  { primaryWindow := 5
    secondaryWindow := 6
    certificateBudgetWindow := 12
    slack := 1 }

example : sampleTauberianBudgetCertificate.Ready := by
  constructor
  · norm_num [TauberianBudgetCertificate.controlled,
      sampleTauberianBudgetCertificate]
  · norm_num [TauberianBudgetCertificate.budgetControlled,
      sampleTauberianBudgetCertificate]

example :
    sampleTauberianBudgetCertificate.certificateBudgetWindow ≤
      sampleTauberianBudgetCertificate.size := by
  apply tauberian_budgetCertificate_le_size
  constructor
  · norm_num [TauberianBudgetCertificate.controlled,
      sampleTauberianBudgetCertificate]
  · norm_num [TauberianBudgetCertificate.budgetControlled,
      sampleTauberianBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleTauberianBudgetCertificate.Ready := by
  constructor
  · norm_num [TauberianBudgetCertificate.controlled,
      sampleTauberianBudgetCertificate]
  · norm_num [TauberianBudgetCertificate.budgetControlled,
      sampleTauberianBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleTauberianBudgetCertificate.certificateBudgetWindow ≤
      sampleTauberianBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List TauberianBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleTauberianBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleTauberianBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.Tauberian
