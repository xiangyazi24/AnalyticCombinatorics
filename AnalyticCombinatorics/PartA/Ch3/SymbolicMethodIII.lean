import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartA.Ch3.SymbolicMethodIII


/-!
# Symbolic method extensions: multivariate GF and parameter analysis

Chapter III uses bivariate generating functions `F(z,u)` to mark a size
variable `z` together with a parameter marker `u`.  The coefficient
`[z^n u^k] F` is the number of size-`n` objects whose marked parameter has
value `k`.

The checks below are finite executable tables: Catalan paths by area,
Stirling-number coefficient arrays, and Lah-number rows.
-/

/-! ## Bivariate coefficient tables -/

/-- A finite executable model of a bivariate generating function. -/
abbrev BivariateGF := Nat → Nat → Nat

/-- `bgfCoeff F n k` represents the coefficient `[z^n u^k] F(z,u)`. -/
def bgfCoeff (F : BivariateGF) (n k : Nat) : Nat :=
  F n k

/-- A sample bivariate series with one nonzero coefficient. -/
def markedToyBGF : BivariateGF :=
  fun n k => if n = 2 ∧ k = 1 then 3 else 0

example : bgfCoeff markedToyBGF 2 1 = 3 := by native_decide
example : bgfCoeff markedToyBGF 2 0 = 0 := by native_decide
example : bgfCoeff markedToyBGF 3 1 = 0 := by native_decide

/-! ## Catalan paths with an area parameter -/

/-- Boolean encoding of up and down steps.  `true` is up, `false` is down. -/
def stepHeight : Bool → Int
  | true => 1
  | false => -1

/-- All Boolean words of a fixed length. -/
def boolWords : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (boolWords n).foldr (fun w acc => (false :: w) :: (true :: w) :: acc) []

/-- Final height of a path. -/
def finalHeight (p : List Bool) : Int :=
  p.foldl (fun h b => h + stepHeight b) 0

/-- Heights after each prefix. -/
def prefixHeightsFrom : List Bool → Int → List Int
  | [], _ => []
  | b :: rest, h =>
      let h' := h + stepHeight b
      h' :: prefixHeightsFrom rest h'

def prefixHeights (p : List Bool) : List Int :=
  prefixHeightsFrom p 0

/-- Dyck paths of semilength `n`, encoded as nonnegative balanced paths. -/
def isDyckPath (n : Nat) (p : List Bool) : Bool :=
  (p.length == 2 * n) &&
    (finalHeight p == 0) &&
      ((prefixHeights p).all fun h => decide (0 ≤ h))

def dyckPaths (n : Nat) : List (List Bool) :=
  (boolWords (2 * n)).filter (isDyckPath n)

/--
Area under a Dyck path, normalized so the zig-zag path has area `0`.
At each down step from height `h`, it adds `h - 1`.
-/
def dyckAreaAux : List Bool → Nat → Nat → Nat
  | [], _, acc => acc
  | true :: rest, h, acc => dyckAreaAux rest (h + 1) acc
  | false :: rest, h, acc => dyckAreaAux rest (h - 1) (acc + (h - 1))

def dyckArea (p : List Bool) : Nat :=
  dyckAreaAux p 0 0

def catalanAreaCount (n area : Nat) : Nat :=
  ((dyckPaths n).filter fun p => dyckArea p == area).length

def catalanAreaRow0 : Fin 1 → ℕ := ![1]
def catalanAreaRow1 : Fin 1 → ℕ := ![1]
def catalanAreaRow2 : Fin 2 → ℕ := ![1, 1]
def catalanAreaRow3 : Fin 4 → ℕ := ![1, 2, 1, 1]

example : (fun i : Fin 1 => catalanAreaCount 0 i) = catalanAreaRow0 := by native_decide
example : (fun i : Fin 1 => catalanAreaCount 1 i) = catalanAreaRow1 := by native_decide
example : (fun i : Fin 2 => catalanAreaCount 2 i) = catalanAreaRow2 := by native_decide
example : (fun i : Fin 4 => catalanAreaCount 3 i) = catalanAreaRow3 := by native_decide

example : (dyckPaths 0).length = 1 := by native_decide
example : (dyckPaths 1).length = 1 := by native_decide
example : (dyckPaths 2).length = 2 := by native_decide
example : (dyckPaths 3).length = 5 := by native_decide

/-! ## Stirling numbers as BGF coefficient tables -/

/-- Stirling numbers of the second kind. -/
def stirlingSecond : Nat → Nat → Nat
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => (k + 1) * stirlingSecond n (k + 1) + stirlingSecond n k

/--
Coefficient table for the block-counting Stirling BGF.  The marker `u`
records the number of blocks, so `[z^n u^k]` gives `S(n,k)`.
-/
def risingStirlingBGFCoeff : BivariateGF :=
  stirlingSecond

def stirlingSecondPositiveRow (n : Nat) : Fin n → Nat :=
  fun k => stirlingSecond n (k + 1)

def stirlingSecondRow1 : Fin 1 → ℕ := ![1]
def stirlingSecondRow2 : Fin 2 → ℕ := ![1, 1]
def stirlingSecondRow3 : Fin 3 → ℕ := ![1, 3, 1]
def stirlingSecondRow4 : Fin 4 → ℕ := ![1, 7, 6, 1]
def stirlingSecondRow5 : Fin 5 → ℕ := ![1, 15, 25, 10, 1]
def stirlingSecondRow6 : Fin 6 → ℕ := ![1, 31, 90, 65, 15, 1]

example : stirlingSecondPositiveRow 1 = stirlingSecondRow1 := by native_decide
example : stirlingSecondPositiveRow 2 = stirlingSecondRow2 := by native_decide
example : stirlingSecondPositiveRow 3 = stirlingSecondRow3 := by native_decide
example : stirlingSecondPositiveRow 4 = stirlingSecondRow4 := by native_decide
example : stirlingSecondPositiveRow 5 = stirlingSecondRow5 := by native_decide
example : stirlingSecondPositiveRow 6 = stirlingSecondRow6 := by native_decide

example : bgfCoeff risingStirlingBGFCoeff 4 2 = 7 := by native_decide
example : bgfCoeff risingStirlingBGFCoeff 5 2 = 15 := by native_decide
example : bgfCoeff risingStirlingBGFCoeff 5 3 = 25 := by native_decide

/-! ## Signed Stirling numbers of the first kind from falling factorials -/

/-- Signed Stirling numbers of the first kind. -/
def signedStirlingFirst : Nat → Nat → Int
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => signedStirlingFirst n k - (n : Int) * signedStirlingFirst n (k + 1)

/--
Coefficient `[z^n u^k]` of `u(u-1)...(u-n+1)/n!`, represented as a rational.
-/
def fallingFactorialCoeffDiv (n k : Nat) : Rat :=
  (signedStirlingFirst n k : Rat) / (Nat.factorial n : Rat)

example : signedStirlingFirst 3 1 = 2 := by native_decide
example : signedStirlingFirst 3 2 = -3 := by native_decide
example : signedStirlingFirst 3 3 = 1 := by native_decide

example : fallingFactorialCoeffDiv 3 1 = (1 : Rat) / 3 := by native_decide
example : fallingFactorialCoeffDiv 3 2 = (-1 : Rat) / 2 := by native_decide
example : fallingFactorialCoeffDiv 3 3 = (1 : Rat) / 6 := by native_decide
example : fallingFactorialCoeffDiv 4 1 = (-1 : Rat) / 4 := by native_decide
example : fallingFactorialCoeffDiv 4 2 = (11 : Rat) / 24 := by native_decide
example : fallingFactorialCoeffDiv 4 3 = (-1 : Rat) / 4 := by native_decide
example : fallingFactorialCoeffDiv 4 4 = (1 : Rat) / 24 := by native_decide

/-! ## Lah numbers -/

/-- Unsigned Lah numbers `L(n,k) = C(n-1,k-1) * n! / k!`. -/
def lahNumber : Nat → Nat → Nat
  | 0, 0 => 1
  | _ + 1, 0 => 0
  | 0, _ + 1 => 0
  | n + 1, k + 1 => Nat.choose n k * Nat.factorial (n + 1) / Nat.factorial (k + 1)

def lahPositiveRow (n : Nat) : Fin n → Nat :=
  fun k => lahNumber n (k + 1)

def lahRowSum (n : Nat) : Nat :=
  (List.range (n + 1)).foldl (fun acc k => acc + lahNumber n k) 0

def lahRow1 : Fin 1 → ℕ := ![1]
def lahRow2 : Fin 2 → ℕ := ![2, 1]
def lahRow3 : Fin 3 → ℕ := ![6, 6, 1]
def lahRow4 : Fin 4 → ℕ := ![24, 36, 12, 1]
def lahRow5 : Fin 5 → ℕ := ![120, 240, 120, 20, 1]

example : lahPositiveRow 1 = lahRow1 := by native_decide
example : lahPositiveRow 2 = lahRow2 := by native_decide
example : lahPositiveRow 3 = lahRow3 := by native_decide
example : lahPositiveRow 4 = lahRow4 := by native_decide
example : lahPositiveRow 5 = lahRow5 := by native_decide

example : lahNumber 3 1 = 6 := by native_decide
example : lahNumber 3 2 = 6 := by native_decide
example : lahNumber 3 3 = 1 := by native_decide
example : lahNumber 4 1 = 24 := by native_decide
example : lahNumber 4 2 = 36 := by native_decide
example : lahNumber 4 3 = 12 := by native_decide
example : lahNumber 4 4 = 1 := by native_decide

example : ∀ n : Fin 6, 1 ≤ (n : Nat) → lahNumber n 1 = Nat.factorial n := by native_decide
example : ∀ n : Fin 6, 1 ≤ (n : Nat) → lahNumber n n = 1 := by native_decide
example : ∀ n : Fin 6, 2 ≤ (n : Nat) → lahNumber n (n - 1) = n * (n - 1) := by
  native_decide

example : lahRowSum 1 = 1 := by native_decide
example : lahRowSum 2 = 3 := by native_decide
example : lahRowSum 3 = 13 := by native_decide
example : lahRowSum 4 = 73 := by native_decide
example : lahRowSum 5 = 501 := by native_decide

/-- Catalan area row sample for semilength three. -/
theorem catalanAreaRow_three :
    (fun i : Fin 4 => catalanAreaCount 3 i) = catalanAreaRow3 := by
  native_decide

/-- Lah row sum sample. -/
theorem lahRowSum_five :
    lahRowSum 5 = 501 := by
  native_decide



structure SymbolicMethodIIIBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SymbolicMethodIIIBudgetCertificate.controlled
    (c : SymbolicMethodIIIBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def SymbolicMethodIIIBudgetCertificate.budgetControlled
    (c : SymbolicMethodIIIBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def SymbolicMethodIIIBudgetCertificate.Ready
    (c : SymbolicMethodIIIBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SymbolicMethodIIIBudgetCertificate.size
    (c : SymbolicMethodIIIBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem symbolicMethodIII_budgetCertificate_le_size
    (c : SymbolicMethodIIIBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSymbolicMethodIIIBudgetCertificate :
    SymbolicMethodIIIBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleSymbolicMethodIIIBudgetCertificate.Ready := by
  constructor
  · norm_num [SymbolicMethodIIIBudgetCertificate.controlled,
      sampleSymbolicMethodIIIBudgetCertificate]
  · norm_num [SymbolicMethodIIIBudgetCertificate.budgetControlled,
      sampleSymbolicMethodIIIBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSymbolicMethodIIIBudgetCertificate.certificateBudgetWindow ≤
      sampleSymbolicMethodIIIBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleSymbolicMethodIIIBudgetCertificate.Ready := by
  constructor
  · norm_num [SymbolicMethodIIIBudgetCertificate.controlled,
      sampleSymbolicMethodIIIBudgetCertificate]
  · norm_num [SymbolicMethodIIIBudgetCertificate.budgetControlled,
      sampleSymbolicMethodIIIBudgetCertificate]

example :
    sampleSymbolicMethodIIIBudgetCertificate.certificateBudgetWindow ≤
      sampleSymbolicMethodIIIBudgetCertificate.size := by
  apply symbolicMethodIII_budgetCertificate_le_size
  constructor
  · norm_num [SymbolicMethodIIIBudgetCertificate.controlled,
      sampleSymbolicMethodIIIBudgetCertificate]
  · norm_num [SymbolicMethodIIIBudgetCertificate.budgetControlled,
      sampleSymbolicMethodIIIBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List SymbolicMethodIIIBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSymbolicMethodIIIBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleSymbolicMethodIIIBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch3.SymbolicMethodIII
