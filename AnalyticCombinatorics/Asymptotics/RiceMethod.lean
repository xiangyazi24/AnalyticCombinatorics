import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Rice method

Finite, decidable bookkeeping for alternating binomial sums, forward
differences, and residue-window certificates used by Rice's method.
-/

namespace AnalyticCombinatorics.Asymptotics.RiceMethod

open Finset

/-- Signed binomial sum appearing in finite Rice transforms. -/
def signedBinomialSum (f : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ k ∈ range (n + 1), (Nat.choose n k : ℤ) * (-1 : ℤ) ^ k * f k

/-- Forward difference with the sign convention matching signed binomial sums. -/
def forwardDifference : ℕ → (ℕ → ℤ) → ℕ → ℤ
  | 0, f, k => f k
  | m + 1, f, k => forwardDifference m f k -
      forwardDifference m f (k + 1)

def constantOneInt (_n : ℕ) : ℤ := 1

def identityInt (n : ℕ) : ℤ := n

def squareInt (n : ℕ) : ℤ := (n : ℤ) ^ 2

def powersTwoInt (n : ℕ) : ℤ := (2 : ℤ) ^ n

def alternatingSignsInt (n : ℕ) : ℤ := (-1 : ℤ) ^ n

theorem signedBinomialSum_constant_samples :
    signedBinomialSum constantOneInt 0 = 1 ∧
      signedBinomialSum constantOneInt 1 = 0 ∧
        signedBinomialSum constantOneInt 5 = 0 := by
  native_decide

theorem signedBinomialSum_identity_samples :
    signedBinomialSum identityInt 0 = 0 ∧
      signedBinomialSum identityInt 1 = -1 ∧
        signedBinomialSum identityInt 2 = 0 ∧
          signedBinomialSum identityInt 5 = 0 := by
  native_decide

theorem signedBinomialSum_square_samples :
    signedBinomialSum squareInt 1 = -1 ∧
      signedBinomialSum squareInt 2 = 2 ∧
        signedBinomialSum squareInt 3 = 0 := by
  native_decide

theorem signedBinomialSum_powersTwo_pair :
    ∀ n : Fin 8,
      signedBinomialSum powersTwoInt n.val = alternatingSignsInt n.val := by
  native_decide

theorem signedBinomialSum_forwardDifference_at_zero :
    ∀ n : Fin 7,
      signedBinomialSum squareInt n.val =
        forwardDifference n.val squareInt 0 := by
  native_decide

/-- Rising factorial denominator for a finite Rice kernel. -/
def risingFactorial : ℕ → ℕ → ℕ
  | _a, 0 => 1
  | a, m + 1 => a * risingFactorial (a + 1) m

theorem risingFactorial_samples :
    (List.range 6).map (risingFactorial 3) =
      [1, 3, 12, 60, 360, 2520] := by
  native_decide

/-- Finite Rice kernel value after clearing the global sign. -/
def riceKernelNumerator (n k : ℕ) : ℤ :=
  (Nat.choose n k : ℤ) * (-1 : ℤ) ^ k

/-- Product `(k + 1) ... (k + n)` used by the pole model. -/
def riceKernelDenominator (n k : ℕ) : ℕ :=
  risingFactorial (k + 1) n

theorem riceKernel_denominator_positive (n k : ℕ) :
    0 < riceKernelDenominator n k := by
  unfold riceKernelDenominator
  induction n generalizing k with
  | zero =>
      simp [risingFactorial]
  | succ n ih =>
      dsimp [risingFactorial]
      exact Nat.mul_pos (Nat.succ_pos k) (ih (k + 1))

def riceKernelValue (n k : ℕ) : ℚ :=
  (riceKernelNumerator n k : ℚ) / (riceKernelDenominator n k : ℚ)

example : riceKernelNumerator 4 2 = 6 := by
  native_decide

example : riceKernelDenominator 4 2 = 360 := by
  native_decide

theorem riceKernelValue_samples :
    riceKernelValue 3 0 = 1 / 6 ∧
      riceKernelValue 3 1 = -1 / 8 ∧
        riceKernelValue 3 2 = 1 / 20 ∧
          riceKernelValue 3 3 = -1 / 120 := by
  native_decide

/-- A finite strip of poles selected for a Rice residue computation. -/
structure RiceResidueWindow where
  poleCount : ℕ
  stripWidth : ℕ
  growthBudget : ℕ
  tailBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RiceResidueWindow.stripControlled (w : RiceResidueWindow) : Prop :=
  0 < w.poleCount ∧ 0 < w.stripWidth

def RiceResidueWindow.tailControlled (w : RiceResidueWindow) : Prop :=
  w.tailBudget ≤ w.stripWidth + w.growthBudget + w.slack

def RiceResidueWindow.ready (w : RiceResidueWindow) : Prop :=
  w.stripControlled ∧ w.tailControlled

def sampleRiceResidueWindow : RiceResidueWindow :=
  { poleCount := 4
    stripWidth := 6
    growthBudget := 3
    tailBudget := 10
    slack := 1 }

theorem sampleRiceResidueWindow_ready :
    sampleRiceResidueWindow.ready := by
  norm_num [RiceResidueWindow.ready, RiceResidueWindow.stripControlled,
    RiceResidueWindow.tailControlled, sampleRiceResidueWindow]

/-- Boolean audit for finite Rice residue windows. -/
def riceResidueWindowListReady (data : List RiceResidueWindow) : Bool :=
  data.all fun w =>
    0 < w.poleCount &&
      0 < w.stripWidth &&
        w.tailBudget ≤ w.stripWidth + w.growthBudget + w.slack

theorem riceResidueWindowList_readyWindow :
    riceResidueWindowListReady
      [sampleRiceResidueWindow,
       { poleCount := 2, stripWidth := 3, growthBudget := 2,
         tailBudget := 5, slack := 0 }] = true := by
  unfold riceResidueWindowListReady sampleRiceResidueWindow
  native_decide

/-- Budget certificate for a finite Rice-method residue computation. -/
structure RiceMethodBudgetCertificate where
  poleWindow : ℕ
  stripWindow : ℕ
  transformWindow : ℕ
  residueWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RiceMethodBudgetCertificate.controlled
    (c : RiceMethodBudgetCertificate) : Prop :=
  0 < c.poleWindow ∧
    0 < c.stripWindow ∧
      c.residueWindow ≤ c.poleWindow + c.transformWindow + c.slack

def RiceMethodBudgetCertificate.budgetControlled
    (c : RiceMethodBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.poleWindow + c.stripWindow + c.transformWindow +
      c.residueWindow + c.slack

def RiceMethodBudgetCertificate.Ready
    (c : RiceMethodBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RiceMethodBudgetCertificate.size
    (c : RiceMethodBudgetCertificate) : ℕ :=
  c.poleWindow + c.stripWindow + c.transformWindow +
    c.residueWindow + c.slack

theorem riceMethod_budgetCertificate_le_size
    (c : RiceMethodBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleRiceMethodBudgetCertificate :
    RiceMethodBudgetCertificate :=
  { poleWindow := 4
    stripWindow := 6
    transformWindow := 5
    residueWindow := 10
    certificateBudgetWindow := 26
    slack := 1 }

example : sampleRiceMethodBudgetCertificate.Ready := by
  constructor
  · norm_num [RiceMethodBudgetCertificate.controlled,
      sampleRiceMethodBudgetCertificate]
  · norm_num [RiceMethodBudgetCertificate.budgetControlled,
      sampleRiceMethodBudgetCertificate]

/-- Finite executable readiness audit for Rice-method budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleRiceMethodBudgetCertificate.Ready := by
  constructor
  · norm_num [RiceMethodBudgetCertificate.controlled,
      sampleRiceMethodBudgetCertificate]
  · norm_num [RiceMethodBudgetCertificate.budgetControlled,
      sampleRiceMethodBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRiceMethodBudgetCertificate.certificateBudgetWindow ≤
      sampleRiceMethodBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List RiceMethodBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleRiceMethodBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleRiceMethodBudgetCertificate
  native_decide

end AnalyticCombinatorics.Asymptotics.RiceMethod
