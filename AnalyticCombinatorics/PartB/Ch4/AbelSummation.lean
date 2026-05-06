import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch4.AbelSummation


/-!
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter IV — Abel Summation and Partial Summation

  Abel summation (discrete integration by parts) relates sums Σ aₖ bₖ
  to partial sums Aₖ = Σ_{j≤k} aⱼ. Applications to Dirichlet series
  coefficient extraction, summatory functions of arithmetic functions,
  and the Euler–Maclaurin summation framework.
-/

/-! ## 1. Forward difference operator and partial sums -/

def forwardDiff (f : ℕ → ℚ) (k : ℕ) : ℚ :=
  f (k + 1) - f k

def partialSum (a : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), a k

def constOne : ℕ → ℚ := fun n => (n : ℚ) - (n : ℚ) + 1
def natId (n : ℕ) : ℚ := ((n : ℕ) : ℚ)
def natSucc (n : ℕ) : ℚ := ((n + 1 : ℕ) : ℚ)
def invSucc (n : ℕ) : ℚ := 1 / ((n + 1 : ℕ) : ℚ)
def sqFn (n : ℕ) : ℚ := ((n * n : ℕ) : ℚ)
def cubeFn (n : ℕ) : ℚ := ((n * n * n : ℕ) : ℚ)
def altSign (n : ℕ) : ℚ := if n % 2 == 0 then 1 else -1

example : forwardDiff natId 0 = 1 := by native_decide
example : forwardDiff natId 7 = 1 := by native_decide
example : forwardDiff sqFn 3 = 7 := by native_decide
example : forwardDiff sqFn 10 = 21 := by native_decide

-- Δ(n²) = 2n + 1
example : ∀ n : Fin 20,
    forwardDiff sqFn n.val = 2 * ((n.val : ℕ) : ℚ) + 1 := by native_decide

example : partialSum constOne 9 = 10 := by native_decide
example : partialSum natSucc 4 = 15 := by native_decide

-- Σ_{k=0}^{n} (k+1) = (n+1)(n+2)/2
example : ∀ n : Fin 15,
    partialSum natSucc n.val =
      (((n.val + 1) * (n.val + 2) : ℕ) : ℚ) / 2 := by native_decide

/-! ### Telescoping: Σ_{k=0}^{n-1} Δf(k) = f(n) - f(0) -/

def telescopeSum (f : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, forwardDiff f k

def telescopeHoldsUpTo (f : ℕ → ℚ) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => telescopeSum f n == f n - f 0

example : telescopeHoldsUpTo sqFn 20 = true := by native_decide
example : telescopeHoldsUpTo cubeFn 15 = true := by native_decide

/-! ## 2. Abel summation formula

  Form 1:  Σ_{k=0}^{n} aₖ bₖ = Aₙ bₙ − Σ_{k=0}^{n−1} Aₖ Δbₖ
  Form 2:  Σ_{k=0}^{n} aₖ bₖ = Aₙ b_{n+1} − Σ_{k=0}^{n} Aₖ Δbₖ -/

def abelLHS (a b : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), a k * b k

def abelRHS1 (a b : ℕ → ℚ) (n : ℕ) : ℚ :=
  partialSum a n * b n -
  ∑ k ∈ Finset.range n, partialSum a k * forwardDiff b k

def abelRHS2 (a b : ℕ → ℚ) (n : ℕ) : ℚ :=
  partialSum a n * b (n + 1) -
  ∑ k ∈ Finset.range (n + 1), partialSum a k * forwardDiff b k

-- aₖ = 1, bₖ = k
example : abelLHS constOne natId 0 = abelRHS1 constOne natId 0 := by native_decide
example : abelLHS constOne natId 5 = abelRHS1 constOne natId 5 := by native_decide
example : abelLHS constOne natId 10 = abelRHS1 constOne natId 10 := by native_decide

-- aₖ = k+1, bₖ = 1/(k+1)
example : abelLHS natSucc invSucc 0 = abelRHS1 natSucc invSucc 0 := by native_decide
example : abelLHS natSucc invSucc 9 = abelRHS1 natSucc invSucc 9 := by native_decide
example : abelLHS natSucc invSucc 9 = 10 := by native_decide

-- aₖ = 1, bₖ = k²
example : abelLHS constOne sqFn 7 = abelRHS1 constOne sqFn 7 := by native_decide
example : abelLHS constOne sqFn 7 = abelRHS2 constOne sqFn 7 := by native_decide

-- aₖ = (-1)^k, bₖ = 1/(k+1)
example : abelLHS altSign invSucc 9 = abelRHS1 altSign invSucc 9 := by native_decide

-- Form 2 verification
example : abelLHS constOne natId 5 = abelRHS2 constOne natId 5 := by native_decide
example : abelLHS natSucc invSucc 9 = abelRHS2 natSucc invSucc 9 := by native_decide

-- Bulk verification
def abelForm1HoldsUpTo (a b : ℕ → ℚ) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => abelLHS a b n == abelRHS1 a b n

def abelForm2HoldsUpTo (a b : ℕ → ℚ) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => abelLHS a b n == abelRHS2 a b n

theorem abel_form1_constOne_sqFn :
    abelForm1HoldsUpTo constOne sqFn 15 = true := by native_decide
theorem abel_form2_constOne_sqFn :
    abelForm2HoldsUpTo constOne sqFn 15 = true := by native_decide
theorem abel_form1_natSucc_invSucc :
    abelForm1HoldsUpTo natSucc invSucc 12 = true := by native_decide
theorem abel_form1_altSign_invSucc :
    abelForm1HoldsUpTo altSign invSucc 15 = true := by native_decide

-- Both forms agree
def bothFormsAgreeUpTo (a b : ℕ → ℚ) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => abelRHS1 a b n == abelRHS2 a b n

theorem both_forms_agree_constOne_sqFn :
    bothFormsAgreeUpTo constOne sqFn 15 = true := by native_decide
theorem both_forms_agree_natSucc_invSucc :
    bothFormsAgreeUpTo natSucc invSucc 12 = true := by native_decide

/-! ## 3. Second-order differences -/

def secondDiff (f : ℕ → ℚ) (k : ℕ) : ℚ :=
  f (k + 2) - 2 * f (k + 1) + f k

-- Δ²(n²) = 2
example : ∀ n : Fin 15, secondDiff sqFn n.val = 2 := by native_decide

-- Δ²(n³) = 6n + 6
example : ∀ n : Fin 15,
    secondDiff cubeFn n.val = 6 * ((n.val : ℕ) : ℚ) + 6 := by native_decide

def doublePartialSum (a : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), partialSum a k

-- A²(n) for constant 1: Σ_{j=0}^n (j+1) = (n+1)(n+2)/2
example : ∀ n : Fin 12,
    doublePartialSum constOne n.val =
      (((n.val + 1) * (n.val + 2) : ℕ) : ℚ) / 2 := by native_decide

/-! ## 4. Harmonic numbers via Abel summation

  Hₙ = Σ_{k=1}^{n} 1/k analyzed through partial summation. -/

def harmonicNumber (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, 1 / ((k + 1 : ℕ) : ℚ)

example : harmonicNumber 1 = 1 := by native_decide
example : harmonicNumber 2 = 3 / 2 := by native_decide
example : harmonicNumber 3 = 11 / 6 := by native_decide
example : harmonicNumber 4 = 25 / 12 := by native_decide
example : harmonicNumber 5 = 137 / 60 := by native_decide
example : harmonicNumber 10 = 7381 / 2520 := by native_decide

-- Consecutive differences strictly decreasing: 1/(n+2) < 1/(n+1)
example : ∀ n : Fin 9,
    harmonicNumber (n.val + 2) - harmonicNumber (n.val + 1) <
    harmonicNumber (n.val + 1) - harmonicNumber n.val := by native_decide

-- Alternating harmonic partial sums (converges to ln 2)
def altHarmonic (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, altSign k / ((k + 1 : ℕ) : ℚ)

example : altHarmonic 1 = 1 := by native_decide
example : altHarmonic 2 = 1 / 2 := by native_decide
example : altHarmonic 4 = 7 / 12 := by native_decide

-- Partial sums oscillate around the limit
example : altHarmonic 2 < altHarmonic 1 := by native_decide
example : altHarmonic 2 < altHarmonic 3 := by native_decide
example : altHarmonic 4 < altHarmonic 3 := by native_decide

-- Hₙ decomposes as abelLHS(1, 1/(k+1))
example : ∀ n : Fin 10,
    harmonicNumber (n.val + 1) = abelLHS constOne invSucc n.val := by native_decide

/-! ## 5. Summatory functions of arithmetic functions -/

def dividesBool (d n : ℕ) : Bool :=
  if d = 0 then false else n % d == 0

def divisorList (n : ℕ) : List ℕ :=
  (List.range (n + 1)).filter (fun d => dividesBool d n)

def isPrimeBool (n : ℕ) : Bool :=
  decide (2 ≤ n) &&
    ((List.range (n + 1)).filter (fun d => decide (2 ≤ d ∧ d < n))).all
      (fun d => !dividesBool d n)

def hasPrimeSquareFactor (n : ℕ) : Bool :=
  (divisorList n).any (fun p => isPrimeBool p && dividesBool (p * p) n)

def primeFactorCount (n : ℕ) : ℕ :=
  ((divisorList n).filter isPrimeBool).length

def mu (n : ℕ) : ℚ :=
  if n = 0 then 0
  else if hasPrimeSquareFactor n then 0
  else if primeFactorCount n % 2 == 0 then 1 else -1

example : mu 1 = 1 := by native_decide
example : mu 2 = -1 := by native_decide
example : mu 6 = 1 := by native_decide
example : mu 4 = 0 := by native_decide
example : mu 30 = -1 := by native_decide

/-! ### Mertens function M(n) = Σ_{k=1}^{n} μ(k) -/

def mertensFunction (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, mu (k + 1)

example : mertensFunction 1 = 1 := by native_decide
example : mertensFunction 2 = 0 := by native_decide
example : mertensFunction 5 = -2 := by native_decide
example : mertensFunction 10 = -1 := by native_decide

theorem mertens_values_1_to_10 :
    (List.range 10).map (fun k => mertensFunction (k + 1)) =
      [1, 0, -1, -1, -2, -1, -2, -2, -2, -1] := by native_decide

/-! ### Divisor summatory function and hyperbola method -/

def numDivisors (n : ℕ) : ℚ := (((divisorList n).length : ℕ) : ℚ)

def divisorSummatory (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, numDivisors (k + 1)

example : divisorSummatory 1 = 1 := by native_decide
example : divisorSummatory 6 = 14 := by native_decide
example : divisorSummatory 10 = 27 := by native_decide

-- D(n) = Σ_{d=1}^{n} ⌊n/d⌋ (equivalent formulation via Abel summation)
def divisorSummatoryAlt (n : ℕ) : ℚ :=
  ∑ d ∈ Finset.range n, (((n / (d + 1) : ℕ) : ℕ) : ℚ)

theorem divisor_summatory_equivalence :
    (List.range 15).map (fun k => divisorSummatory (k + 1)) =
    (List.range 15).map (fun k => divisorSummatoryAlt (k + 1)) := by native_decide

-- Dirichlet hyperbola method: D(n) = 2·Σ_{d≤√n} ⌊n/d⌋ − ⌊√n⌋²
def hyperbolaSum (n : ℕ) : ℚ :=
  let s := Nat.sqrt n
  2 * ∑ d ∈ Finset.range s, (((n / (d + 1) : ℕ) : ℕ) : ℚ) - (((s * s : ℕ) : ℕ) : ℚ)

theorem hyperbola_method_1_to_15 :
    (List.range 15).map (fun k => divisorSummatory (k + 1)) =
    (List.range 15).map (fun k => hyperbolaSum (k + 1)) := by native_decide

/-! ## 6. Dirichlet series and Abel summation

  Abel summation applied to Σ a(n)/n gives:
  Σ_{n=1}^{N} a(n)/n = A(N)/N + Σ_{k=1}^{N-1} A(k)/(k(k+1))
  where A(k) = Σ_{j=1}^{k} a(j). -/

def dirichletCumSum (a : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range n, a (j + 1)

def dirichletPartialSum (a : ℕ → ℚ) (N : ℕ) : ℚ :=
  ∑ k ∈ Finset.range N, a (k + 1) / ((k + 1 : ℕ) : ℚ)

def dirichletAbelForm (a : ℕ → ℚ) (N : ℕ) : ℚ :=
  dirichletCumSum a N / ((N : ℕ) : ℚ) +
  ∑ k ∈ Finset.range (N - 1),
    dirichletCumSum a (k + 1) / (((k + 1) * (k + 2) : ℕ) : ℚ)

def dirichletAbelHoldsUpTo (a : ℕ → ℚ) (N : ℕ) : Bool :=
  ((List.range N).map (fun k => k + 1)).all fun n =>
    dirichletPartialSum a n == dirichletAbelForm a n

-- For constant coefficients: Σ 1/n = H_N
theorem dirichlet_abel_constOne :
    dirichletAbelHoldsUpTo constOne 12 = true := by native_decide

-- For Möbius coefficients: Σ μ(n)/n via Mertens partial sums
theorem dirichlet_abel_mu :
    dirichletAbelHoldsUpTo mu 8 = true := by native_decide

-- Connection: dirichletCumSum μ = Mertens function
example : ∀ n : Fin 10,
    dirichletCumSum mu n.val = mertensFunction n.val := by native_decide

/-! ## 7. Bernoulli numbers and Euler–Maclaurin summation -/

def bernoulliList : ℕ → List ℚ
  | 0 => [1]
  | (n + 1) =>
    let prev := bernoulliList n
    let m := n + 1
    let bPrev : ℕ → ℚ := fun k => prev.getD k 0
    let s := ((List.range m).map (fun k =>
      ((Nat.choose (m + 1) k : ℕ) : ℚ) * bPrev k)).sum
    prev ++ [-s / ((m + 1 : ℕ) : ℚ)]

def bernoulli (n : ℕ) : ℚ := (bernoulliList n).getD n 0

example : bernoulli 0 = 1 := by native_decide
example : bernoulli 1 = -1 / 2 := by native_decide
example : bernoulli 2 = 1 / 6 := by native_decide
example : bernoulli 3 = 0 := by native_decide
example : bernoulli 4 = -1 / 30 := by native_decide
example : bernoulli 6 = 1 / 42 := by native_decide
example : bernoulli 8 = -1 / 30 := by native_decide

-- Odd Bernoulli numbers vanish for index ≥ 3
example : ∀ k : Fin 5,
    bernoulli (2 * k.val + 3) = 0 := by native_decide

-- EM coefficients match B_{2j}/(2j)!
example : bernoulli 2 / ((Nat.factorial 2 : ℕ) : ℚ) = 1 / 12 := by native_decide
example : bernoulli 4 / ((Nat.factorial 4 : ℕ) : ℚ) = -1 / 720 := by native_decide
example : bernoulli 6 / ((Nat.factorial 6 : ℕ) : ℚ) = 1 / 30240 := by native_decide

/-! ### Euler–Maclaurin: Σ f(k) = ∫f + (f(0)+f(n))/2 + B₂/2!·(f'(n)−f'(0)) + ... -/

def eulerMaclaurin1 (f integral f' : ℕ → ℚ) (n : ℕ) : ℚ :=
  integral n + (f 0 + f n) / 2 + (1 / 12) * (f' n - f' 0)

def eulerMaclaurin2 (f integral f' f''' : ℕ → ℚ) (n : ℕ) : ℚ :=
  integral n + (f 0 + f n) / 2 + (1 / 12) * (f' n - f' 0) -
  (1 / 720) * (f''' n - f''' 0)

-- Σ k² via EM1 (exact for degree ≤ 3)
def sumOfSquares (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), ((k * k : ℕ) : ℚ)

example : ∀ n : Fin 15,
    sumOfSquares n.val = eulerMaclaurin1 sqFn
      (fun n => ((n * n * n : ℕ) : ℚ) / 3)
      (fun n => 2 * ((n : ℕ) : ℚ)) n.val := by native_decide

-- Σ k³ via EM1 (exact for degree ≤ 3)
def sumOfCubes (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), ((k * k * k : ℕ) : ℚ)

example : ∀ n : Fin 15,
    sumOfCubes n.val = eulerMaclaurin1 cubeFn
      (fun n => ((n * n * n * n : ℕ) : ℚ) / 4)
      (fun n => 3 * ((n * n : ℕ) : ℚ)) n.val := by native_decide

-- Niesen's identity: Σ k³ = [n(n+1)/2]²
example : ∀ n : Fin 15,
    sumOfCubes n.val =
      ((n.val * (n.val + 1) / 2 : ℕ) : ℚ) *
      ((n.val * (n.val + 1) / 2 : ℕ) : ℚ) := by native_decide

-- EM1 is NOT exact for degree 4
def fourthPowerFn (n : ℕ) : ℚ := ((n * n * n * n : ℕ) : ℚ)
def sumOfFourthPowers (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), fourthPowerFn k

example : sumOfFourthPowers 2 ≠
    eulerMaclaurin1 fourthPowerFn
      (fun n => ((n * n * n * n * n : ℕ) : ℚ) / 5)
      (fun n => 4 * ((n * n * n : ℕ) : ℚ)) 2 := by native_decide

-- EM2 with B₄ correction IS exact for degree 4
example : ∀ n : Fin 12,
    sumOfFourthPowers n.val = eulerMaclaurin2 fourthPowerFn
      (fun n => ((n * n * n * n * n : ℕ) : ℚ) / 5)
      (fun n => 4 * ((n * n * n : ℕ) : ℚ))
      (fun n => 24 * ((n : ℕ) : ℚ)) n.val := by native_decide

/-! ## 8. Deeper theorems -/

theorem abel_summation_identity :
    abelForm1HoldsUpTo constOne sqFn 15 = true ∧
    abelForm1HoldsUpTo natSucc invSucc 12 = true := by
  native_decide

theorem abel_summation_identity' :
    abelForm2HoldsUpTo constOne sqFn 15 = true ∧
    abelForm2HoldsUpTo natSucc invSucc 12 = true := by
  native_decide

theorem telescoping_identity :
    telescopeHoldsUpTo sqFn 20 = true ∧ telescopeHoldsUpTo cubeFn 15 = true := by
  native_decide

theorem bernoulli_recurrence :
    ∀ n : Fin 8,
      1 ≤ n.val →
      ((List.range (n.val + 1)).map (fun k =>
        ((Nat.choose (n.val + 1) k : ℕ) : ℚ) * bernoulli k)).sum = 0 := by
  native_decide

theorem sum_of_first_n :
    ∀ n : Fin 20,
      ∑ k ∈ Finset.range (n.val + 1), ((k : ℕ) : ℚ) =
        ((n.val : ℕ) : ℚ) * (((n.val : ℕ) : ℚ) + 1) / 2 := by
  native_decide

theorem sum_of_squares_formula :
    ∀ n : Fin 20,
      sumOfSquares n.val =
        ((n.val : ℕ) : ℚ) * (((n.val : ℕ) : ℚ) + 1) *
          (2 * ((n.val : ℕ) : ℚ) + 1) / 6 := by
  native_decide

theorem dirichlet_abel_formula :
    ∀ N : Fin 12,
      1 ≤ N.val →
        dirichletPartialSum constOne N.val = dirichletAbelForm constOne N.val := by
  native_decide

theorem hyperbola_method_exact :
    ∀ n : Fin 12, 1 ≤ n.val → divisorSummatory n.val = hyperbolaSum n.val := by
  native_decide

theorem mertens_bound :
    ∀ n : Fin 20, |mertensFunction n.val| ≤ ((n.val : ℕ) : ℚ) := by
  native_decide



structure AbelSummationBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AbelSummationBudgetCertificate.controlled
    (c : AbelSummationBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AbelSummationBudgetCertificate.budgetControlled
    (c : AbelSummationBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AbelSummationBudgetCertificate.Ready
    (c : AbelSummationBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AbelSummationBudgetCertificate.size
    (c : AbelSummationBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem abelSummation_budgetCertificate_le_size
    (c : AbelSummationBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAbelSummationBudgetCertificate :
    AbelSummationBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleAbelSummationBudgetCertificate.Ready := by
  constructor
  · norm_num [AbelSummationBudgetCertificate.controlled,
      sampleAbelSummationBudgetCertificate]
  · norm_num [AbelSummationBudgetCertificate.budgetControlled,
      sampleAbelSummationBudgetCertificate]

example :
    sampleAbelSummationBudgetCertificate.certificateBudgetWindow ≤
      sampleAbelSummationBudgetCertificate.size := by
  apply abelSummation_budgetCertificate_le_size
  constructor
  · norm_num [AbelSummationBudgetCertificate.controlled,
      sampleAbelSummationBudgetCertificate]
  · norm_num [AbelSummationBudgetCertificate.budgetControlled,
      sampleAbelSummationBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleAbelSummationBudgetCertificate.Ready := by
  constructor
  · norm_num [AbelSummationBudgetCertificate.controlled,
      sampleAbelSummationBudgetCertificate]
  · norm_num [AbelSummationBudgetCertificate.budgetControlled,
      sampleAbelSummationBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAbelSummationBudgetCertificate.certificateBudgetWindow ≤
      sampleAbelSummationBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List AbelSummationBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAbelSummationBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAbelSummationBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch4.AbelSummation
