import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch9.UrnsAndBalls


section BallsIntoBins

/-- Number of functions from `n` labelled balls to `k` labelled bins. -/
def ballsIntoBins (k n : ℕ) : ℕ := k ^ n

/-- Selected balls-into-bins counts. -/
def ballsIntoBinsTable : Fin 4 → ℕ := ![81, 64, 3125, 1024]

example : ballsIntoBins 3 4 = 81 := by native_decide
example : ballsIntoBins 4 3 = 64 := by native_decide
example : ballsIntoBins 5 5 = 3125 := by native_decide
example : ballsIntoBins 2 10 = 1024 := by native_decide

example : ballsIntoBinsTable ⟨0, by omega⟩ = ballsIntoBins 3 4 := by native_decide
example : ballsIntoBinsTable ⟨1, by omega⟩ = ballsIntoBins 4 3 := by native_decide
example : ballsIntoBinsTable ⟨2, by omega⟩ = ballsIntoBins 5 5 := by native_decide
example : ballsIntoBinsTable ⟨3, by omega⟩ = ballsIntoBins 2 10 := by native_decide

end BallsIntoBins

section StirlingAndBell

/-- Stirling numbers of the second kind. -/
def stirling2 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => (k + 1) * stirling2 n (k + 1) + stirling2 n k

/-- Selected Stirling number values:
`S2(4,2)`, `S2(4,3)`, `S2(5,2)`, `S2(5,3)`, `S2(5,4)`. -/
def stirling2Table : Fin 5 → ℕ := ![7, 6, 15, 25, 10]

example : stirling2 4 2 = 7 := by native_decide
example : stirling2 4 3 = 6 := by native_decide
example : stirling2 5 2 = 15 := by native_decide
example : stirling2 5 3 = 25 := by native_decide
example : stirling2 5 4 = 10 := by native_decide

example : stirling2Table ⟨0, by omega⟩ = stirling2 4 2 := by native_decide
example : stirling2Table ⟨1, by omega⟩ = stirling2 4 3 := by native_decide
example : stirling2Table ⟨2, by omega⟩ = stirling2 5 2 := by native_decide
example : stirling2Table ⟨3, by omega⟩ = stirling2 5 3 := by native_decide
example : stirling2Table ⟨4, by omega⟩ = stirling2 5 4 := by native_decide

/-- Bell number as a finite sum of Stirling numbers of the second kind. -/
def bell (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), stirling2 n k

/-- Selected Bell numbers: `B(4)` and `B(5)`. -/
def bellTable : Fin 2 → ℕ := ![15, 52]

example : bell 4 = 15 := by native_decide
example : bell 5 = 52 := by native_decide

example : bellTable ⟨0, by omega⟩ = bell 4 := by native_decide
example : bellTable ⟨1, by omega⟩ = bell 5 := by native_decide

end StirlingAndBell

section Birthday

/-- Number of unordered pairs among `n` people. -/
def birthdayPairs (n : ℕ) : ℕ := Nat.choose n 2

/-- Selected birthday pair counts. -/
def birthdayPairsTable : Fin 2 → ℕ := ![66430, 253]

example : birthdayPairs 365 = 66430 := by native_decide
example : birthdayPairs 23 = 253 := by native_decide

example : birthdayPairsTable ⟨0, by omega⟩ = birthdayPairs 365 := by native_decide
example : birthdayPairsTable ⟨1, by omega⟩ = birthdayPairs 23 := by native_decide

end Birthday

section ScaledHarmonics

/-- Integer-scaled harmonic number `n! * H(n)`. -/
def scaledHarmonic (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, Nat.factorial n / (k + 1)

/-- Values of `n! * H(n)` for `n = 1..7`. -/
def scaledHarmonicTable : Fin 7 → ℕ := ![1, 3, 11, 50, 274, 1764, 13068]

example : scaledHarmonic 1 = 1 := by native_decide
example : scaledHarmonic 2 = 3 := by native_decide
example : scaledHarmonic 3 = 11 := by native_decide
example : scaledHarmonic 4 = 50 := by native_decide
example : scaledHarmonic 5 = 274 := by native_decide
example : scaledHarmonic 6 = 1764 := by native_decide
example : scaledHarmonic 7 = 13068 := by native_decide

example : scaledHarmonicTable ⟨0, by omega⟩ = scaledHarmonic 1 := by native_decide
example : scaledHarmonicTable ⟨1, by omega⟩ = scaledHarmonic 2 := by native_decide
example : scaledHarmonicTable ⟨2, by omega⟩ = scaledHarmonic 3 := by native_decide
example : scaledHarmonicTable ⟨3, by omega⟩ = scaledHarmonic 4 := by native_decide
example : scaledHarmonicTable ⟨4, by omega⟩ = scaledHarmonic 5 := by native_decide
example : scaledHarmonicTable ⟨5, by omega⟩ = scaledHarmonic 6 := by native_decide
example : scaledHarmonicTable ⟨6, by omega⟩ = scaledHarmonic 7 := by native_decide

end ScaledHarmonics

section PowersOfTwo

/-- Powers of two for exponents `1..10`. -/
def powersOfTwoTable : Fin 10 → ℕ := ![2, 4, 8, 16, 32, 64, 128, 256, 512, 1024]

example : 2 ^ 1 = 2 := by native_decide
example : 2 ^ 2 = 4 := by native_decide
example : 2 ^ 3 = 8 := by native_decide
example : 2 ^ 4 = 16 := by native_decide
example : 2 ^ 5 = 32 := by native_decide
example : 2 ^ 6 = 64 := by native_decide
example : 2 ^ 7 = 128 := by native_decide
example : 2 ^ 8 = 256 := by native_decide
example : 2 ^ 9 = 512 := by native_decide
example : 2 ^ 10 = 1024 := by native_decide

example : powersOfTwoTable ⟨0, by omega⟩ = 2 ^ 1 := by native_decide
example : powersOfTwoTable ⟨1, by omega⟩ = 2 ^ 2 := by native_decide
example : powersOfTwoTable ⟨2, by omega⟩ = 2 ^ 3 := by native_decide
example : powersOfTwoTable ⟨3, by omega⟩ = 2 ^ 4 := by native_decide
example : powersOfTwoTable ⟨4, by omega⟩ = 2 ^ 5 := by native_decide
example : powersOfTwoTable ⟨5, by omega⟩ = 2 ^ 6 := by native_decide
example : powersOfTwoTable ⟨6, by omega⟩ = 2 ^ 7 := by native_decide
example : powersOfTwoTable ⟨7, by omega⟩ = 2 ^ 8 := by native_decide
example : powersOfTwoTable ⟨8, by omega⟩ = 2 ^ 9 := by native_decide
example : powersOfTwoTable ⟨9, by omega⟩ = 2 ^ 10 := by native_decide

end PowersOfTwo

section Multinomials

/-- Multinomial coefficient as a factorial quotient. -/
def multinomial3 (n a b c : ℕ) : ℕ :=
  Nat.factorial n / (Nat.factorial a * Nat.factorial b * Nat.factorial c)

/-- Multinomial coefficient for two parts. -/
def multinomial2 (n a b : ℕ) : ℕ :=
  Nat.factorial n / (Nat.factorial a * Nat.factorial b)

/-- Selected multinomial coefficients. -/
def multinomialTable : Fin 3 → ℕ := ![90, 60, 6]

example : multinomial3 6 2 2 2 = 90 := by native_decide
example : multinomial3 6 3 2 1 = 60 := by native_decide
example : multinomial2 4 2 2 = 6 := by native_decide

example : Nat.factorial 6 / (Nat.factorial 2 * Nat.factorial 2 * Nat.factorial 2) = 90 := by
  native_decide

example : Nat.factorial 6 / (Nat.factorial 3 * Nat.factorial 2 * Nat.factorial 1) = 60 := by
  native_decide

example : Nat.factorial 4 / (Nat.factorial 2 * Nat.factorial 2) = 6 := by
  native_decide

example : multinomialTable ⟨0, by omega⟩ = multinomial3 6 2 2 2 := by native_decide
example : multinomialTable ⟨1, by omega⟩ = multinomial3 6 3 2 1 := by native_decide
example : multinomialTable ⟨2, by omega⟩ = multinomial2 4 2 2 := by native_decide

end Multinomials

/-- Integer-scaled harmonic sample. -/
theorem scaledHarmonic_seven :
    scaledHarmonic 7 = 13068 := by
  native_decide

/-- Three-part multinomial sample. -/
theorem multinomial3_six_balanced :
    multinomial3 6 2 2 2 = 90 := by
  native_decide



structure UrnsAndBallsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UrnsAndBallsBudgetCertificate.controlled
    (c : UrnsAndBallsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def UrnsAndBallsBudgetCertificate.budgetControlled
    (c : UrnsAndBallsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def UrnsAndBallsBudgetCertificate.Ready
    (c : UrnsAndBallsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UrnsAndBallsBudgetCertificate.size
    (c : UrnsAndBallsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem urnsAndBalls_budgetCertificate_le_size
    (c : UrnsAndBallsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUrnsAndBallsBudgetCertificate :
    UrnsAndBallsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleUrnsAndBallsBudgetCertificate.Ready := by
  constructor
  · norm_num [UrnsAndBallsBudgetCertificate.controlled,
      sampleUrnsAndBallsBudgetCertificate]
  · norm_num [UrnsAndBallsBudgetCertificate.budgetControlled,
      sampleUrnsAndBallsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUrnsAndBallsBudgetCertificate.certificateBudgetWindow ≤
      sampleUrnsAndBallsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleUrnsAndBallsBudgetCertificate.Ready := by
  constructor
  · norm_num [UrnsAndBallsBudgetCertificate.controlled,
      sampleUrnsAndBallsBudgetCertificate]
  · norm_num [UrnsAndBallsBudgetCertificate.budgetControlled,
      sampleUrnsAndBallsBudgetCertificate]

example :
    sampleUrnsAndBallsBudgetCertificate.certificateBudgetWindow ≤
      sampleUrnsAndBallsBudgetCertificate.size := by
  apply urnsAndBalls_budgetCertificate_le_size
  constructor
  · norm_num [UrnsAndBallsBudgetCertificate.controlled,
      sampleUrnsAndBallsBudgetCertificate]
  · norm_num [UrnsAndBallsBudgetCertificate.budgetControlled,
      sampleUrnsAndBallsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List UrnsAndBallsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUrnsAndBallsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleUrnsAndBallsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch9.UrnsAndBalls
