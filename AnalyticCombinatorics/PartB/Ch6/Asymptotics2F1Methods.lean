import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch6.Asymptotics2F1Methods


/-!
  Hypergeometric 2F1 methods from Chapter VI, represented here by
  computable rational finite checks.  The analytic identities are recorded
  through their integer/rational specializations and coefficient tests.
-/

/-! ## Basic computable ingredients -/

/-- Rising factorial `(a)_n = a (a+1) ... (a+n-1)` over `ℚ`. -/
def pochhammerQ (a : ℚ) (n : ℕ) : ℚ :=
  (Finset.range n).prod fun k => a + k

/-- The `n`th coefficient term of `2F1(a,b;c;z)`. -/
def twoFoneTerm (a b c : ℚ) (n : ℕ) : ℚ :=
  pochhammerQ a n * pochhammerQ b n / (pochhammerQ c n * Nat.factorial n)

/-- The first `N` terms of `2F1(a,b;c;z)`, indexed by `0 ≤ n < N`. -/
def twoFonePartial (a b c z : ℚ) (N : ℕ) : ℚ :=
  (Finset.range N).sum fun n => twoFoneTerm a b c n * z ^ n

/-- Integer Gamma values, as rationals: `Γ(n) = (n-1)!` for positive integers. -/
def gammaPosQ (n : ℕ) : ℚ :=
  Nat.factorial (n - 1)

/-- The right side of Gauss's unit argument formula for positive integer data. -/
def gaussUnitRHS (a b c : ℕ) : ℚ :=
  gammaPosQ c * gammaPosQ (c - a - b) / (gammaPosQ (c - a) * gammaPosQ (c - b))

/-! ## 1. Gauss unit argument formula: `2F1(a,b;c;1)` -/

/-- The condition `c > a + b` in the sample Gauss unit argument. -/
example : (1 : ℕ) + 1 < 3 := by native_decide

/-- `Γ(3)Γ(1)/(Γ(2)Γ(2)) = 2`. -/
example : gaussUnitRHS 1 1 3 = 2 := by native_decide

/-- Direct Gamma-factor verification: `2 * 1 / (1 * 1) = 2`. -/
example : gammaPosQ 3 * gammaPosQ 1 / (gammaPosQ 2 * gammaPosQ 2) = 2 := by
  native_decide

/-- Terms of `2F1(1,1;3;1)`: `(1)_n (1)_n / ((3)_n n!)`. -/
example : twoFoneTerm 1 1 3 0 = 1 := by native_decide
example : twoFoneTerm 1 1 3 1 = 1 / 3 := by native_decide
example : twoFoneTerm 1 1 3 2 = 1 / 6 := by native_decide
example : twoFoneTerm 1 1 3 3 = 1 / 10 := by native_decide
example : twoFoneTerm 1 1 3 4 = 1 / 15 := by native_decide
example : twoFoneTerm 1 1 3 5 = 1 / 21 := by native_decide

/-- Partial sums for `Σ (1)_n (1)_n / ((3)_n n!)`; the limit is `2`. -/
example : twoFonePartial 1 1 3 1 1 = 1 := by native_decide
example : twoFonePartial 1 1 3 1 2 = 4 / 3 := by native_decide
example : twoFonePartial 1 1 3 1 3 = 3 / 2 := by native_decide
example : twoFonePartial 1 1 3 1 4 = 8 / 5 := by native_decide
example : twoFonePartial 1 1 3 1 5 = 5 / 3 := by native_decide
example : twoFonePartial 1 1 3 1 6 = 12 / 7 := by native_decide
example : twoFonePartial 1 1 3 1 10 = 20 / 11 := by native_decide
example : twoFonePartial 1 1 3 1 20 = 40 / 21 := by native_decide
example : twoFonePartial 1 1 3 1 20 < 2 := by native_decide

/-! ## 2. Pochhammer symbol checks -/

example : pochhammerQ 1 1 = 1 := by native_decide
example : pochhammerQ 1 2 = 2 := by native_decide
example : pochhammerQ 1 3 = 6 := by native_decide
example : pochhammerQ 1 4 = 24 := by native_decide
example : pochhammerQ 1 5 = 120 := by native_decide

example : pochhammerQ 2 1 = 2 := by native_decide
example : pochhammerQ 2 2 = 6 := by native_decide
example : pochhammerQ 2 3 = 24 := by native_decide
example : pochhammerQ 2 4 = 120 := by native_decide
example : pochhammerQ 2 5 = 720 := by native_decide

example : pochhammerQ 3 1 = 3 := by native_decide
example : pochhammerQ 3 2 = 12 := by native_decide
example : pochhammerQ 3 3 = 60 := by native_decide
example : pochhammerQ 3 4 = 360 := by native_decide
example : pochhammerQ 3 5 = 2520 := by native_decide

example : pochhammerQ 4 1 = 4 := by native_decide
example : pochhammerQ 4 2 = 20 := by native_decide
example : pochhammerQ 4 3 = 120 := by native_decide
example : pochhammerQ 4 4 = 840 := by native_decide
example : pochhammerQ 4 5 = 6720 := by native_decide

example : pochhammerQ 5 1 = 5 := by native_decide
example : pochhammerQ 5 2 = 30 := by native_decide
example : pochhammerQ 5 3 = 210 := by native_decide
example : pochhammerQ 5 4 = 1680 := by native_decide
example : pochhammerQ 5 5 = 15120 := by native_decide

/-! ## 3. Vandermonde identity: terminating `2F1(-n,b;c;1)` -/

/-- The terminating left side of Vandermonde's identity. -/
def vandermondeLHS (n : ℕ) (b c : ℚ) : ℚ :=
  twoFonePartial (-(n : ℚ)) b c 1 (n + 1)

/-- The right side `(c-b)_n/(c)_n`. -/
def vandermondeRHS (n : ℕ) (b c : ℚ) : ℚ :=
  pochhammerQ (c - b) n / pochhammerQ c n

example : vandermondeLHS 0 1 3 = vandermondeRHS 0 1 3 := by native_decide
example : vandermondeLHS 1 1 3 = vandermondeRHS 1 1 3 := by native_decide
example : vandermondeLHS 2 1 3 = vandermondeRHS 2 1 3 := by native_decide
example : vandermondeLHS 3 1 3 = vandermondeRHS 3 1 3 := by native_decide
example : vandermondeLHS 4 1 3 = vandermondeRHS 4 1 3 := by native_decide

example : vandermondeLHS 1 2 5 = vandermondeRHS 1 2 5 := by native_decide
example : vandermondeLHS 2 2 5 = vandermondeRHS 2 2 5 := by native_decide
example : vandermondeLHS 3 2 5 = vandermondeRHS 3 2 5 := by native_decide
example : vandermondeLHS 4 2 5 = vandermondeRHS 4 2 5 := by native_decide

example : vandermondeLHS 3 1 3 = 2 / 5 := by native_decide
example : vandermondeLHS 4 2 5 = 3 / 14 := by native_decide

/-! ## 4. Chu-Vandermonde convolution -/

/-- Chu-Vandermonde convolution in the special coefficient form. -/
def chuVandermondeSum (m n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sum fun k => Nat.choose m k * Nat.choose n (n - k)

example : Nat.choose (3 + 2) 2 = chuVandermondeSum 3 2 := by native_decide
example : Nat.choose (4 + 3) 3 = chuVandermondeSum 4 3 := by native_decide
example : Nat.choose (5 + 4) 4 = chuVandermondeSum 5 4 := by native_decide
example : Nat.choose (6 + 2) 2 = chuVandermondeSum 6 2 := by native_decide

/-- Special central-binomial case `C(2n,n) = Σ_k C(n,k) C(n,n-k)`. -/
example : Nat.choose (2 * 2) 2 = chuVandermondeSum 2 2 := by native_decide
example : Nat.choose (2 * 3) 3 = chuVandermondeSum 3 3 := by native_decide
example : Nat.choose (2 * 4) 4 = chuVandermondeSum 4 4 := by native_decide
example : Nat.choose (2 * 5) 5 = chuVandermondeSum 5 5 := by native_decide

example : chuVandermondeSum 3 2 = 1 + 6 + 3 := by native_decide
example : chuVandermondeSum 4 3 = 1 + 12 + 18 + 4 := by native_decide

/-! ## 5. Gauss contiguous relations: coefficient checks -/

/-- Coefficient form of `F(a+1,b;c;z) = F(a,b;c;z) + (b z/c) F(a+1,b+1;c+1;z)`. -/
abbrev contiguousACoeffHolds (a b c : ℚ) (n : ℕ) : Prop :=
  twoFoneTerm (a + 1) b c n =
    twoFoneTerm a b c n +
      if n = 0 then 0 else (b / c) * twoFoneTerm (a + 1) (b + 1) (c + 1) (n - 1)

/-- Symmetric coefficient form shifting `b`. -/
abbrev contiguousBCoeffHolds (a b c : ℚ) (n : ℕ) : Prop :=
  twoFoneTerm a (b + 1) c n =
    twoFoneTerm a b c n +
      if n = 0 then 0 else (a / c) * twoFoneTerm (a + 1) (b + 1) (c + 1) (n - 1)

example : contiguousACoeffHolds 1 2 5 0 := by native_decide
example : contiguousACoeffHolds 1 2 5 1 := by native_decide
example : contiguousACoeffHolds 1 2 5 2 := by native_decide
example : contiguousACoeffHolds 1 2 5 3 := by native_decide
example : contiguousACoeffHolds 1 2 5 4 := by native_decide
example : contiguousACoeffHolds 1 2 5 5 := by native_decide

example : contiguousBCoeffHolds 2 1 5 0 := by native_decide
example : contiguousBCoeffHolds 2 1 5 1 := by native_decide
example : contiguousBCoeffHolds 2 1 5 2 := by native_decide
example : contiguousBCoeffHolds 2 1 5 3 := by native_decide
example : contiguousBCoeffHolds 2 1 5 4 := by native_decide
example : contiguousBCoeffHolds 2 1 5 5 := by native_decide

/-! ## 6. Kummer/Euler transformation: coefficient checks -/

/-- Coefficient of `(1-z)^r`. -/
def oneMinusZCoeff (r j : ℕ) : ℚ :=
  if j ≤ r then (-1 : ℚ) ^ j * Nat.choose r j else 0

/-- Coefficient of `(1-z)^r * 2F1(c-a,c-b;c;z)` at `z^n`. -/
def kummerRHSCoeff (a b c : ℚ) (r n : ℕ) : ℚ :=
  (Finset.range (n + 1)).sum fun j =>
    oneMinusZCoeff r j * twoFoneTerm (c - a) (c - b) c (n - j)

/-- Coefficient equality for `2F1(a,b;c;z) = (1-z)^r 2F1(c-a,c-b;c;z)`. -/
abbrev kummerCoeffHolds (a b c : ℚ) (r n : ℕ) : Prop :=
  twoFoneTerm a b c n = kummerRHSCoeff a b c r n

/-- Here `r = c-a-b = 1` for `a=b=1,c=3`. -/
example : kummerCoeffHolds 1 1 3 1 0 := by native_decide
example : kummerCoeffHolds 1 1 3 1 1 := by native_decide
example : kummerCoeffHolds 1 1 3 1 2 := by native_decide
example : kummerCoeffHolds 1 1 3 1 3 := by native_decide
example : kummerCoeffHolds 1 1 3 1 4 := by native_decide
example : kummerCoeffHolds 1 1 3 1 5 := by native_decide

/-- Another integer case: `r = c-a-b = 2` for `a=1,b=2,c=5`. -/
example : kummerCoeffHolds 1 2 5 2 0 := by native_decide
example : kummerCoeffHolds 1 2 5 2 1 := by native_decide
example : kummerCoeffHolds 1 2 5 2 2 := by native_decide
example : kummerCoeffHolds 1 2 5 2 3 := by native_decide
example : kummerCoeffHolds 1 2 5 2 4 := by native_decide
example : kummerCoeffHolds 1 2 5 2 5 := by native_decide

example : oneMinusZCoeff 2 0 = 1 := by native_decide
example : oneMinusZCoeff 2 1 = -2 := by native_decide
example : oneMinusZCoeff 2 2 = 1 := by native_decide
example : oneMinusZCoeff 2 3 = 0 := by native_decide

/-- Gauss unit argument sample. -/
theorem gaussUnitRHS_one_one_three :
    gaussUnitRHS 1 1 3 = 2 := by
  native_decide

/-- A terminating Vandermonde sample. -/
theorem vandermondeLHS_four_two_five :
    vandermondeLHS 4 2 5 = 3 / 14 := by
  native_decide

/-- Chu-Vandermonde central-binomial sample. -/
theorem chuVandermondeSum_five_five :
    chuVandermondeSum 5 5 = Nat.choose 10 5 := by
  native_decide

/-- Kummer coefficient sample. -/
theorem kummerCoeffHolds_sample :
    kummerCoeffHolds 1 2 5 2 5 := by
  native_decide



structure Asymptotics2F1MethodsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def Asymptotics2F1MethodsBudgetCertificate.controlled
    (c : Asymptotics2F1MethodsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def Asymptotics2F1MethodsBudgetCertificate.budgetControlled
    (c : Asymptotics2F1MethodsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def Asymptotics2F1MethodsBudgetCertificate.Ready
    (c : Asymptotics2F1MethodsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def Asymptotics2F1MethodsBudgetCertificate.size
    (c : Asymptotics2F1MethodsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem asymptotics2F1Methods_budgetCertificate_le_size
    (c : Asymptotics2F1MethodsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAsymptotics2F1MethodsBudgetCertificate :
    Asymptotics2F1MethodsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleAsymptotics2F1MethodsBudgetCertificate.Ready := by
  constructor
  · norm_num [Asymptotics2F1MethodsBudgetCertificate.controlled,
      sampleAsymptotics2F1MethodsBudgetCertificate]
  · norm_num [Asymptotics2F1MethodsBudgetCertificate.budgetControlled,
      sampleAsymptotics2F1MethodsBudgetCertificate]

example :
    sampleAsymptotics2F1MethodsBudgetCertificate.certificateBudgetWindow ≤
      sampleAsymptotics2F1MethodsBudgetCertificate.size := by
  apply asymptotics2F1Methods_budgetCertificate_le_size
  constructor
  · norm_num [Asymptotics2F1MethodsBudgetCertificate.controlled,
      sampleAsymptotics2F1MethodsBudgetCertificate]
  · norm_num [Asymptotics2F1MethodsBudgetCertificate.budgetControlled,
      sampleAsymptotics2F1MethodsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleAsymptotics2F1MethodsBudgetCertificate.Ready := by
  constructor
  · norm_num [Asymptotics2F1MethodsBudgetCertificate.controlled,
      sampleAsymptotics2F1MethodsBudgetCertificate]
  · norm_num [Asymptotics2F1MethodsBudgetCertificate.budgetControlled,
      sampleAsymptotics2F1MethodsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAsymptotics2F1MethodsBudgetCertificate.certificateBudgetWindow ≤
      sampleAsymptotics2F1MethodsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List Asymptotics2F1MethodsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAsymptotics2F1MethodsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAsymptotics2F1MethodsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch6.Asymptotics2F1Methods
