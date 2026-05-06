import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartA.Ch3.MultivarGF


/-- Bivariate sequence representing [x^n u^k] F(x,u) -/
def BivariateSeq := ℕ → ℕ → ℤ

def coeff (f : BivariateSeq) (n k : ℕ) : ℤ := f n k

/-- Total count: [x^n] F(x,1) = Σ_k f(n,k) -/
def totalCount (f : BivariateSeq) (n : ℕ) (bound : ℕ) : ℤ :=
  (Finset.range bound).sum (fun k => f n k)

/-- Cumulative parameter: [x^n] (∂F/∂u)|_{u=1} = Σ_k k·f(n,k) -/
def cumulativeParam (f : BivariateSeq) (n : ℕ) (bound : ℕ) : ℤ :=
  (Finset.range bound).sum (fun k => (↑k : ℤ) * f n k)

/-- Mean parameter value as a rational -/
def meanParam (f : BivariateSeq) (n : ℕ) (bound : ℕ) : ℚ :=
  (↑(cumulativeParam f n bound) : ℚ) / (↑(totalCount f n bound) : ℚ)

/-- Second factorial moment: Σ_k k(k-1)·f(n,k) -/
def secondFactorialMoment (f : BivariateSeq) (n : ℕ) (bound : ℕ) : ℤ :=
  (Finset.range bound).sum (fun k => (↑(k * (k - 1)) : ℤ) * f n k)

/-- Bivariate convolution: product of two BGFs -/
def bivConv (f g : BivariateSeq) : BivariateSeq := fun n k =>
  (Finset.range (n + 1)).sum (fun i =>
    (Finset.range (k + 1)).sum (fun j => f i j * g (n - i) (k - j)))

/-! ## Example 1: Binary words — F(x,u) = 1/(1-x(1+u))
  Words over {0,1} of length n with k ones: [x^n u^k] = C(n,k) -/

def binaryWords : BivariateSeq := fun n k => ↑(Nat.choose n k)

example : coeff binaryWords 0 0 = 1 := by native_decide
example : coeff binaryWords 3 0 = 1 := by native_decide
example : coeff binaryWords 3 1 = 3 := by native_decide
example : coeff binaryWords 3 2 = 3 := by native_decide
example : coeff binaryWords 3 3 = 1 := by native_decide
example : coeff binaryWords 4 2 = 6 := by native_decide
example : coeff binaryWords 5 3 = 10 := by native_decide

example : totalCount binaryWords 3 4 = 8 := by native_decide
example : totalCount binaryWords 4 5 = 16 := by native_decide
example : totalCount binaryWords 5 6 = 32 := by native_decide

-- Cumulative: Σ k·C(n,k) = n·2^(n-1)
example : cumulativeParam binaryWords 3 4 = 12 := by native_decide
example : cumulativeParam binaryWords 4 5 = 32 := by native_decide
example : cumulativeParam binaryWords 5 6 = 80 := by native_decide

-- Mean number of 1s in a binary word of length n is n/2
example : meanParam binaryWords 4 5 = 2 := by native_decide
example : meanParam binaryWords 6 7 = 3 := by native_decide

-- Second factorial moment: Σ k(k-1)·C(n,k) = n(n-1)·2^(n-2)
example : secondFactorialMoment binaryWords 4 5 = 48 := by native_decide
example : secondFactorialMoment binaryWords 5 6 = 160 := by native_decide

/-! ## Example 2: Compositions — F(x,u) = (1-x)/(1-x-ux)
  Compositions of n into k parts: [x^n u^k] = C(n-1, k-1) for n,k ≥ 1 -/

def compositions : BivariateSeq := fun n k =>
  if n = 0 then (if k = 0 then 1 else 0)
  else if k = 0 then 0
  else ↑(Nat.choose (n - 1) (k - 1))

example : coeff compositions 0 0 = 1 := by native_decide
example : coeff compositions 3 1 = 1 := by native_decide
example : coeff compositions 3 2 = 2 := by native_decide
example : coeff compositions 3 3 = 1 := by native_decide
example : coeff compositions 4 2 = 3 := by native_decide
example : coeff compositions 5 2 = 4 := by native_decide

-- Total compositions of n: 2^(n-1)
example : totalCount compositions 3 4 = 4 := by native_decide
example : totalCount compositions 4 5 = 8 := by native_decide
example : totalCount compositions 5 6 = 16 := by native_decide

-- Cumulative number of parts: Σ k·C(n-1,k-1) = (n+1)·2^(n-2) for n ≥ 2
example : cumulativeParam compositions 3 4 = 8 := by native_decide
example : cumulativeParam compositions 4 5 = 20 := by native_decide
example : cumulativeParam compositions 5 6 = 48 := by native_decide

/-! ## Example 3: Ternary words — F(x,u) = 1/(1-x(u+2))
  Words over {a,b,c} of length n with k occurrences of 'a': C(n,k)·2^(n-k) -/

def ternaryWords : BivariateSeq := fun n k =>
  ↑(Nat.choose n k * 2^(n - k))

example : coeff ternaryWords 2 0 = 4 := by native_decide
example : coeff ternaryWords 2 1 = 4 := by native_decide
example : coeff ternaryWords 2 2 = 1 := by native_decide
example : coeff ternaryWords 3 1 = 12 := by native_decide
example : coeff ternaryWords 4 0 = 16 := by native_decide

-- Total: 3^n
example : totalCount ternaryWords 3 4 = 27 := by native_decide
example : totalCount ternaryWords 4 5 = 81 := by native_decide

-- Cumulative: Σ k·C(n,k)·2^(n-k) = n·3^(n-1)
example : cumulativeParam ternaryWords 3 4 = 27 := by native_decide
example : cumulativeParam ternaryWords 4 5 = 108 := by native_decide

-- Mean occurrences of 'a' in ternary word of length n is n/3
example : meanParam ternaryWords 3 4 = 1 := by native_decide
example : meanParam ternaryWords 6 7 = 2 := by native_decide

/-! ## Convolution identity
  Product: 1/(1-x) · 1/(1-xu) = 1/((1-x)(1-xu))
  [x^n u^k] 1/(1-x) = δ_{k,0}, [x^n u^k] 1/(1-xu) = δ_{n,k}
  [x^n u^k] product = 1 if k ≤ n, 0 otherwise -/

def geomConst : BivariateSeq := fun n k => if k = 0 then ((n - n : ℕ) : ℤ) + 1 else 0

def geomMarked : BivariateSeq := fun n k => if n = k then 1 else 0

example : bivConv geomConst geomMarked 3 0 = 1 := by native_decide
example : bivConv geomConst geomMarked 3 1 = 1 := by native_decide
example : bivConv geomConst geomMarked 3 2 = 1 := by native_decide
example : bivConv geomConst geomMarked 3 3 = 1 := by native_decide
example : bivConv geomConst geomMarked 3 4 = 0 := by native_decide
example : bivConv geomConst geomMarked 4 2 = 1 := by native_decide
example : bivConv geomConst geomMarked 4 5 = 0 := by native_decide

-- Delta sequence is convolution identity
def delta : BivariateSeq := fun n k => if n = 0 ∧ k = 0 then 1 else 0

example : bivConv delta binaryWords 3 2 = coeff binaryWords 3 2 := by native_decide
example : bivConv delta ternaryWords 2 1 = coeff ternaryWords 2 1 := by native_decide

/-! ## Marginal extraction: fixing one variable -/

def marginalN (f : BivariateSeq) (k : ℕ) : ℕ → ℤ := fun n => f n k

def marginalK (f : BivariateSeq) (n : ℕ) : ℕ → ℤ := fun k => f n k

-- The k-th marginal of binaryWords gives the k-th column of Pascal's triangle
example : marginalN binaryWords 2 3 = 3 := by native_decide
example : marginalN binaryWords 2 4 = 6 := by native_decide
example : marginalN binaryWords 2 5 = 10 := by native_decide

/-! ## Theorem: binary words total count equals 2^n -/

theorem binaryWords_total (n : ℕ) :
    totalCount binaryWords n (n + 1) = 2 ^ n := by
  simp only [totalCount, binaryWords]
  have h := Nat.sum_range_choose n
  exact_mod_cast h

/-! ## Cumulative parameter theorem for binary words -/

theorem binaryWords_cumulative_eq :
    ∀ n : Fin 10,
      cumulativeParam binaryWords n.val (n.val + 1) = ↑n.val * 2 ^ (n.val - 1) := by
  native_decide

/-! ## Diagonal extraction: [x^n u^n] F(x,u) -/

def diagonal (f : BivariateSeq) : ℕ → ℤ := fun n => f n n

example : diagonal binaryWords 0 = 1 := by native_decide
example : diagonal binaryWords 3 = 1 := by native_decide
example : diagonal ternaryWords 2 = 1 := by native_decide
example : diagonal compositions 4 = 1 := by native_decide

/-! ## Partial derivative operator (discrete): Δ_u f(n,k) = (k+1)·f(n,k+1)
  This corresponds to differentiation ∂F/∂u in the GF world -/

def diffU (f : BivariateSeq) : BivariateSeq := fun n k =>
  (↑(k + 1) : ℤ) * f n (k + 1)

-- For binaryWords: (∂/∂u)(1/(1-x(1+u))) evaluated gives related BGF
-- [x^n u^k] of ∂F/∂u = (k+1)·C(n, k+1)
example : diffU binaryWords 4 0 = 4 := by native_decide
example : diffU binaryWords 4 1 = 12 := by native_decide
example : diffU binaryWords 4 2 = 12 := by native_decide
example : diffU binaryWords 4 3 = 4 := by native_decide



structure MultivarGFBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MultivarGFBudgetCertificate.controlled
    (c : MultivarGFBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def MultivarGFBudgetCertificate.budgetControlled
    (c : MultivarGFBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def MultivarGFBudgetCertificate.Ready
    (c : MultivarGFBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def MultivarGFBudgetCertificate.size
    (c : MultivarGFBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem multivarGF_budgetCertificate_le_size
    (c : MultivarGFBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleMultivarGFBudgetCertificate :
    MultivarGFBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleMultivarGFBudgetCertificate.Ready := by
  constructor
  · norm_num [MultivarGFBudgetCertificate.controlled,
      sampleMultivarGFBudgetCertificate]
  · norm_num [MultivarGFBudgetCertificate.budgetControlled,
      sampleMultivarGFBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleMultivarGFBudgetCertificate.certificateBudgetWindow ≤
      sampleMultivarGFBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleMultivarGFBudgetCertificate.Ready := by
  constructor
  · norm_num [MultivarGFBudgetCertificate.controlled,
      sampleMultivarGFBudgetCertificate]
  · norm_num [MultivarGFBudgetCertificate.budgetControlled,
      sampleMultivarGFBudgetCertificate]

example :
    sampleMultivarGFBudgetCertificate.certificateBudgetWindow ≤
      sampleMultivarGFBudgetCertificate.size := by
  apply multivarGF_budgetCertificate_le_size
  constructor
  · norm_num [MultivarGFBudgetCertificate.controlled,
      sampleMultivarGFBudgetCertificate]
  · norm_num [MultivarGFBudgetCertificate.budgetControlled,
      sampleMultivarGFBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List MultivarGFBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleMultivarGFBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleMultivarGFBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch3.MultivarGF
