import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Appendix A: Combinatorial Sums

Finite binomial, Stirling, and convolution sums used throughout symbolic and
analytic enumeration.
-/

namespace AnalyticCombinatorics.AppA.CombinatorialSums

def binomialRowSum (n : ℕ) : ℕ :=
  (List.range (n + 1)).foldl (fun s k => s + n.choose k) 0

theorem binomialRowSum_samples :
    (List.range 8).map binomialRowSum = [1, 2, 4, 8, 16, 32, 64, 128] := by
  native_decide

def alternatingBinomialRowSum (n : ℕ) : ℤ :=
  (List.range (n + 1)).foldl
    (fun s k => s + (-1 : ℤ) ^ k * (n.choose k : ℤ)) 0

theorem alternatingBinomialRowSum_samples :
    (List.range 7).map alternatingBinomialRowSum = [1, 0, 0, 0, 0, 0, 0] := by
  native_decide

def vandermondeSum (r s n : ℕ) : ℕ :=
  (List.range (n + 1)).foldl (fun acc k => acc + r.choose k * s.choose (n - k)) 0

theorem vandermonde_samples :
    vandermondeSum 3 4 0 = 1 ∧
    vandermondeSum 3 4 2 = 21 ∧
    vandermondeSum 5 6 4 = 330 := by
  native_decide

def stirlingSecond : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => (k + 1) * stirlingSecond n (k + 1) + stirlingSecond n k

theorem stirlingSecond_rows :
    (List.range 6).map (stirlingSecond 5) = [0, 1, 15, 25, 10, 1] := by
  native_decide

def bellFromStirling (n : ℕ) : ℕ :=
  (List.range (n + 1)).foldl (fun s k => s + stirlingSecond n k) 0

theorem bellFromStirling_samples :
    (List.range 7).map bellFromStirling = [1, 1, 2, 5, 15, 52, 203] := by
  native_decide

def ConvolutionSumStatement
    (a b : ℕ → ℕ) (closedForm : ℕ → ℕ) (N : ℕ) : Prop :=
  (List.range (N + 1)).all (fun n =>
    (List.range (n + 1)).foldl (fun s k => s + a k * b (n - k)) 0 = closedForm n) = true

theorem convolution_sum_statement :
    ConvolutionSumStatement (fun _ => 1) (fun _ => 1) (fun n => n + 1) 8 := by
  unfold ConvolutionSumStatement
  native_decide


structure CombinatorialSumsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CombinatorialSumsBudgetCertificate.controlled
    (c : CombinatorialSumsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def CombinatorialSumsBudgetCertificate.budgetControlled
    (c : CombinatorialSumsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def CombinatorialSumsBudgetCertificate.Ready
    (c : CombinatorialSumsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CombinatorialSumsBudgetCertificate.size
    (c : CombinatorialSumsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem combinatorialSums_budgetCertificate_le_size
    (c : CombinatorialSumsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleCombinatorialSumsBudgetCertificate :
    CombinatorialSumsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleCombinatorialSumsBudgetCertificate.Ready := by
  constructor
  · norm_num [CombinatorialSumsBudgetCertificate.controlled,
      sampleCombinatorialSumsBudgetCertificate]
  · norm_num [CombinatorialSumsBudgetCertificate.budgetControlled,
      sampleCombinatorialSumsBudgetCertificate]

example :
    sampleCombinatorialSumsBudgetCertificate.certificateBudgetWindow ≤
      sampleCombinatorialSumsBudgetCertificate.size := by
  apply combinatorialSums_budgetCertificate_le_size
  constructor
  · norm_num [CombinatorialSumsBudgetCertificate.controlled,
      sampleCombinatorialSumsBudgetCertificate]
  · norm_num [CombinatorialSumsBudgetCertificate.budgetControlled,
      sampleCombinatorialSumsBudgetCertificate]

/-- Finite executable readiness audit for combinatorial-sum certificates. -/
def combinatorialSumsBudgetCertificateListReady
    (data : List CombinatorialSumsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem combinatorialSumsBudgetCertificateList_readyWindow :
    combinatorialSumsBudgetCertificateListReady
      [sampleCombinatorialSumsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold combinatorialSumsBudgetCertificateListReady
    sampleCombinatorialSumsBudgetCertificate
  native_decide

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleCombinatorialSumsBudgetCertificate.Ready := by
  constructor
  · norm_num [CombinatorialSumsBudgetCertificate.controlled,
      sampleCombinatorialSumsBudgetCertificate]
  · norm_num [CombinatorialSumsBudgetCertificate.budgetControlled,
      sampleCombinatorialSumsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCombinatorialSumsBudgetCertificate.certificateBudgetWindow ≤
      sampleCombinatorialSumsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List CombinatorialSumsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCombinatorialSumsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleCombinatorialSumsBudgetCertificate
  native_decide
end AnalyticCombinatorics.AppA.CombinatorialSums
