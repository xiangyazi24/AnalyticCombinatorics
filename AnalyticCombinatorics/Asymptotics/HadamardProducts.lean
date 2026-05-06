import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Coefficientwise bounds for Hadamard products.

These statements isolate the elementary order reasoning used by analytic
Hadamard product estimates.
-/

namespace AnalyticCombinatorics.Asymptotics.HadamardProducts

def pointwiseProduct (a b : ℕ → ℕ) (n : ℕ) : ℕ :=
  a n * b n

def boundedBy (a A : ℕ → ℕ) : Prop :=
  ∀ n, a n ≤ A n

def eventuallyZero (a : ℕ → ℕ) (N : ℕ) : Prop :=
  ∀ n, N < n → a n = 0

theorem pointwiseProduct_bound {a b A B : ℕ → ℕ}
    (ha : boundedBy a A) (hb : boundedBy b B) :
    boundedBy (pointwiseProduct a b) (pointwiseProduct A B) := by
  intro n
  exact Nat.mul_le_mul (ha n) (hb n)

theorem eventuallyZero_pointwise_left {a b : ℕ → ℕ} {N : ℕ}
    (ha : eventuallyZero a N) :
    eventuallyZero (pointwiseProduct a b) N := by
  intro n hn
  simp [pointwiseProduct, ha n hn]

theorem eventuallyZero_pointwise_right {a b : ℕ → ℕ} {N : ℕ}
    (hb : eventuallyZero b N) :
    eventuallyZero (pointwiseProduct a b) N := by
  intro n hn
  simp [pointwiseProduct, hb n hn]

def sampleA : ℕ → ℕ
  | 0 => 2
  | 1 => 3
  | _ => 0

def sampleB : ℕ → ℕ
  | 0 => 5
  | 1 => 7
  | _ => 0

example : pointwiseProduct sampleA sampleB 0 = 10 := by
  native_decide

example : pointwiseProduct sampleA sampleB 1 = 21 := by
  native_decide

example : eventuallyZero (pointwiseProduct sampleA sampleB) 1 := by
  intro n hn
  cases n with
  | zero => omega
  | succ n =>
      cases n with
      | zero => omega
      | succ n =>
          simp [pointwiseProduct, sampleA, sampleB]

/-- A finite certificate for Hadamard product coefficient bounds. -/
structure HadamardProductCertificate where
  leftBound : ℕ
  rightBound : ℕ
  productBound : ℕ
  supportWindow : ℕ
  slack : ℕ

/-- The product bound absorbs the pointwise product up to slack. -/
def hadamardProductCertificateControlled
    (w : HadamardProductCertificate) : Prop :=
  w.leftBound * w.rightBound ≤ w.productBound + w.slack

/-- Readiness for a Hadamard product certificate. -/
def hadamardProductCertificateReady
    (w : HadamardProductCertificate) : Prop :=
  hadamardProductCertificateControlled w ∧
    w.productBound ≤ w.leftBound * w.rightBound + w.supportWindow + w.slack

/-- Total size of a Hadamard product certificate. -/
def hadamardProductCertificateSize
    (w : HadamardProductCertificate) : ℕ :=
  w.leftBound + w.rightBound + w.productBound + w.supportWindow + w.slack

theorem hadamardProductCertificate_product_le_size
    (w : HadamardProductCertificate)
    (h : hadamardProductCertificateReady w) :
    w.productBound ≤ hadamardProductCertificateSize w := by
  rcases h with ⟨_, hbudget⟩
  unfold hadamardProductCertificateSize
  omega

def sampleHadamardProductCertificate : HadamardProductCertificate where
  leftBound := 3
  rightBound := 7
  productBound := 21
  supportWindow := 1
  slack := 0

example :
    hadamardProductCertificateReady sampleHadamardProductCertificate := by
  norm_num [hadamardProductCertificateReady,
    hadamardProductCertificateControlled, sampleHadamardProductCertificate]

example :
    sampleHadamardProductCertificate.productBound ≤
      hadamardProductCertificateSize sampleHadamardProductCertificate := by
  apply hadamardProductCertificate_product_le_size
  norm_num [hadamardProductCertificateReady,
    hadamardProductCertificateControlled, sampleHadamardProductCertificate]

/-- Finite executable readiness audit for Hadamard product certificates. -/
def hadamardProductCertificateListReady
    (certs : List HadamardProductCertificate) : Bool :=
  certs.all fun c =>
    c.leftBound * c.rightBound ≤ c.productBound + c.slack &&
      c.productBound ≤ c.leftBound * c.rightBound + c.supportWindow + c.slack

theorem hadamardProductCertificateList_readyWindow :
    hadamardProductCertificateListReady
      [{ leftBound := 2, rightBound := 5, productBound := 10,
         supportWindow := 1, slack := 0 },
       { leftBound := 3, rightBound := 7, productBound := 21,
         supportWindow := 1, slack := 0 }] = true := by
  unfold hadamardProductCertificateListReady
  native_decide

structure HadamardProductRefinementCertificate where
  leftBound : ℕ
  rightBound : ℕ
  productBound : ℕ
  supportWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def HadamardProductRefinementCertificate.productControlled
    (c : HadamardProductRefinementCertificate) : Prop :=
  c.leftBound * c.rightBound ≤ c.productBound + c.slack

def HadamardProductRefinementCertificate.supportControlled
    (c : HadamardProductRefinementCertificate) : Prop :=
  c.supportWindow ≤ c.leftBound + c.rightBound + c.productBound + c.slack

def hadamardProductRefinementReady
    (c : HadamardProductRefinementCertificate) : Prop :=
  c.productControlled ∧ c.supportControlled

def HadamardProductRefinementCertificate.size
    (c : HadamardProductRefinementCertificate) : ℕ :=
  c.leftBound + c.rightBound + c.productBound + c.slack

theorem hadamardProduct_supportWindow_le_size
    {c : HadamardProductRefinementCertificate}
    (h : hadamardProductRefinementReady c) :
    c.supportWindow ≤ c.size := by
  rcases h with ⟨_, hsupport⟩
  exact hsupport

def sampleHadamardProductRefinementCertificate :
    HadamardProductRefinementCertificate :=
  { leftBound := 3, rightBound := 7, productBound := 21,
    supportWindow := 31, slack := 0 }

example : hadamardProductRefinementReady
    sampleHadamardProductRefinementCertificate := by
  norm_num [hadamardProductRefinementReady,
    HadamardProductRefinementCertificate.productControlled,
    HadamardProductRefinementCertificate.supportControlled,
    sampleHadamardProductRefinementCertificate]

example :
    sampleHadamardProductRefinementCertificate.supportWindow ≤
      sampleHadamardProductRefinementCertificate.size := by
  norm_num [HadamardProductRefinementCertificate.size,
    sampleHadamardProductRefinementCertificate]

structure HadamardProductBudgetCertificate where
  leftBound : ℕ
  rightBound : ℕ
  productBound : ℕ
  supportWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def HadamardProductBudgetCertificate.controlled
    (c : HadamardProductBudgetCertificate) : Prop :=
  c.leftBound * c.rightBound ≤ c.productBound + c.slack ∧
    c.supportWindow ≤ c.leftBound + c.rightBound + c.productBound + c.slack

def HadamardProductBudgetCertificate.budgetControlled
    (c : HadamardProductBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.leftBound + c.rightBound + c.productBound + c.supportWindow + c.slack

def HadamardProductBudgetCertificate.Ready
    (c : HadamardProductBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def HadamardProductBudgetCertificate.size
    (c : HadamardProductBudgetCertificate) : ℕ :=
  c.leftBound + c.rightBound + c.productBound + c.supportWindow + c.slack

theorem hadamardProduct_budgetCertificate_le_size
    (c : HadamardProductBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleHadamardProductBudgetCertificate :
    HadamardProductBudgetCertificate :=
  { leftBound := 3
    rightBound := 7
    productBound := 21
    supportWindow := 31
    certificateBudgetWindow := 62
    slack := 0 }

example : sampleHadamardProductBudgetCertificate.Ready := by
  constructor
  · norm_num [HadamardProductBudgetCertificate.controlled,
      sampleHadamardProductBudgetCertificate]
  · norm_num [HadamardProductBudgetCertificate.budgetControlled,
      sampleHadamardProductBudgetCertificate]

example :
    sampleHadamardProductBudgetCertificate.certificateBudgetWindow ≤
      sampleHadamardProductBudgetCertificate.size := by
  apply hadamardProduct_budgetCertificate_le_size
  constructor
  · norm_num [HadamardProductBudgetCertificate.controlled,
      sampleHadamardProductBudgetCertificate]
  · norm_num [HadamardProductBudgetCertificate.budgetControlled,
      sampleHadamardProductBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleHadamardProductBudgetCertificate.Ready := by
  constructor
  · norm_num [HadamardProductBudgetCertificate.controlled,
      sampleHadamardProductBudgetCertificate]
  · norm_num [HadamardProductBudgetCertificate.budgetControlled,
      sampleHadamardProductBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleHadamardProductBudgetCertificate.certificateBudgetWindow ≤
      sampleHadamardProductBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List HadamardProductBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleHadamardProductBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleHadamardProductBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.HadamardProducts
