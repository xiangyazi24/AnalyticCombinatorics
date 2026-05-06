import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Karamata Tauberian windows.
-/

namespace AnalyticCombinatorics.Asymptotics.KaramataTauberian

/-- Partial sums over a finite prefix. -/
def partialSumQ (a : ℕ → ℚ) (n : ℕ) : ℚ :=
  (List.range (n + 1)).foldl (fun s k => s + a k) 0

/-- Finite nonnegativity audit for rational coefficient sequences. -/
def nonnegativeUpToQ (a : ℕ → ℚ) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => 0 ≤ a n

/-- Finite monotonicity audit for rational partial sums. -/
def partialSumsMonotoneUpTo (a : ℕ → ℚ) (N : ℕ) : Bool :=
  (List.range N).all fun n => partialSumQ a n ≤ partialSumQ a (n + 1)

/--
Finite Karamata-style window: nonnegative coefficients, monotone partial
sums, and polynomial doubling control for the sampled summatory function.
-/
def karamataWindowCheck (a : ℕ → ℚ) (N : ℕ) : Bool :=
  nonnegativeUpToQ a N &&
    partialSumsMonotoneUpTo a N &&
      ((List.range (N + 1)).all fun n =>
        if n = 0 then true
        else partialSumQ a (2 * n) ≤ 4 * partialSumQ a n)

def KaramataWindow (a : ℕ → ℚ) (N : ℕ) : Prop :=
  karamataWindowCheck a N = true

theorem partialSumQ_constant_window :
    partialSumQ (fun _ => 1) 0 = 1 ∧
    partialSumQ (fun _ => 1) 1 = 2 ∧
    partialSumQ (fun _ => 1) 2 = 3 ∧
    partialSumQ (fun _ => 1) 3 = 4 := by
  unfold partialSumQ
  native_decide

theorem constant_sequence_karamataWindow :
    KaramataWindow (fun _ => 1) 24 := by
  unfold KaramataWindow karamataWindowCheck nonnegativeUpToQ
    partialSumsMonotoneUpTo partialSumQ
  native_decide

theorem linear_sequence_karamataWindow :
    KaramataWindow (fun n => (n + 1 : ℚ)) 24 := by
  unfold KaramataWindow karamataWindowCheck nonnegativeUpToQ
    partialSumsMonotoneUpTo partialSumQ
  native_decide

example : partialSumQ (fun n => (n + 1 : ℚ)) 3 = 10 := by
  unfold partialSumQ
  native_decide

example : karamataWindowCheck (fun _ => 1) 8 = true := by
  unfold karamataWindowCheck nonnegativeUpToQ
    partialSumsMonotoneUpTo partialSumQ
  native_decide

structure KaramataTauberianBudgetCertificate where
  variationWindow : ℕ
  summatoryWindow : ℕ
  tauberianWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def KaramataTauberianBudgetCertificate.controlled
    (c : KaramataTauberianBudgetCertificate) : Prop :=
  0 < c.variationWindow ∧
    c.tauberianWindow ≤ c.variationWindow + c.summatoryWindow + c.slack

def KaramataTauberianBudgetCertificate.budgetControlled
    (c : KaramataTauberianBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.variationWindow + c.summatoryWindow + c.tauberianWindow + c.slack

def KaramataTauberianBudgetCertificate.Ready
    (c : KaramataTauberianBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def KaramataTauberianBudgetCertificate.size
    (c : KaramataTauberianBudgetCertificate) : ℕ :=
  c.variationWindow + c.summatoryWindow + c.tauberianWindow + c.slack

theorem karamataTauberian_budgetCertificate_le_size
    (c : KaramataTauberianBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleKaramataTauberianBudgetCertificate :
    KaramataTauberianBudgetCertificate :=
  { variationWindow := 5
    summatoryWindow := 6
    tauberianWindow := 10
    certificateBudgetWindow := 22
    slack := 1 }

example : sampleKaramataTauberianBudgetCertificate.Ready := by
  constructor
  · norm_num [KaramataTauberianBudgetCertificate.controlled,
      sampleKaramataTauberianBudgetCertificate]
  · norm_num [KaramataTauberianBudgetCertificate.budgetControlled,
      sampleKaramataTauberianBudgetCertificate]

/-- Finite executable readiness audit for Karamata-Tauberian certificates. -/
def karamataTauberianCertificateListReady
    (certs : List KaramataTauberianBudgetCertificate) : Bool :=
  certs.all fun c =>
    0 < c.variationWindow &&
      c.tauberianWindow ≤ c.variationWindow + c.summatoryWindow + c.slack &&
        c.certificateBudgetWindow ≤
          c.variationWindow + c.summatoryWindow + c.tauberianWindow + c.slack

theorem karamataTauberianCertificateList_readyWindow :
    karamataTauberianCertificateListReady
      [{ variationWindow := 3, summatoryWindow := 4, tauberianWindow := 6,
         certificateBudgetWindow := 13, slack := 0 },
       { variationWindow := 5, summatoryWindow := 6, tauberianWindow := 10,
         certificateBudgetWindow := 22, slack := 1 }] = true := by
  unfold karamataTauberianCertificateListReady
  native_decide

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleKaramataTauberianBudgetCertificate.Ready := by
  constructor
  · norm_num [KaramataTauberianBudgetCertificate.controlled,
      sampleKaramataTauberianBudgetCertificate]
  · norm_num [KaramataTauberianBudgetCertificate.budgetControlled,
      sampleKaramataTauberianBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleKaramataTauberianBudgetCertificate.certificateBudgetWindow ≤
      sampleKaramataTauberianBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List KaramataTauberianBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleKaramataTauberianBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleKaramataTauberianBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.KaramataTauberian
