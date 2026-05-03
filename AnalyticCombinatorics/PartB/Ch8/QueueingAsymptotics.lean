import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace QueueingAsymptotics

/-!
  Queueing theory asymptotics and busy periods from Chapter VIII of
  Analytic Combinatorics, recorded as finite computable checks.
-/

/-! ## M/M/1 queue stationary probabilities -/

/-- M/M/1 stationary probability P(N = n) = (1 - rho) * rho^n. -/
def mm1Probability (rho : ℚ) (n : ℕ) : ℚ :=
  (1 - rho) * rho ^ n

/-- Partial mass through N customers. -/
def mm1PartialSum (rho : ℚ) (N : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (N + 1), mm1Probability rho k

/-- Closed form for the finite geometric mass. -/
def mm1GeometricMass (rho : ℚ) (N : ℕ) : ℚ :=
  1 - rho ^ (N + 1)

/-- Values of Σ_{k=0}^N (1/2) * (1/2)^k for N = 0 .. 10. -/
def mm1HalfPartialTable : Fin 11 → ℚ :=
  ![1 / 2, 3 / 4, 7 / 8, 15 / 16, 31 / 32, 63 / 64,
    127 / 128, 255 / 256, 511 / 512, 1023 / 1024, 2047 / 2048]

/-- Verify Σ_{k=0}^N (1 - rho) * rho^k = 1 - rho^(N+1) at rho = 1/2, N = 0 .. 10. -/
theorem mm1_half_partial_sums :
    ∀ N : Fin 11,
      mm1PartialSum (1 / 2) (N : ℕ) = mm1GeometricMass (1 / 2) (N : ℕ) ∧
        mm1PartialSum (1 / 2) (N : ℕ) = mm1HalfPartialTable N := by
  native_decide

/-! ## Expected queue length -/

/-- M/M/1 expected queue length E[N] = rho / (1 - rho). -/
def mm1ExpectedLength (rho : ℚ) : ℚ :=
  rho / (1 - rho)

theorem mm1_expected_rho_one_third :
    mm1ExpectedLength (1 / 3) = 1 / 2 := by
  native_decide

theorem mm1_expected_rho_one_half :
    mm1ExpectedLength (1 / 2) = 1 := by
  native_decide

/-! ## Busy periods and Catalan numbers -/

/-- Catalan number C_n = binom(2n,n)/(n+1). -/
def catalan (n : ℕ) : ℕ :=
  Nat.choose (2 * n) n / (n + 1)

/-- Number of simple-queue busy periods of length n. -/
def busyPeriodCount (n : ℕ) : ℕ :=
  Nat.choose (2 * n) n / (n + 1)

/-- Catalan values C_1 .. C_8 for busy periods. -/
def busyPeriodTable : Fin 8 → ℕ :=
  ![1, 2, 5, 14, 42, 132, 429, 1430]

/-- Busy periods of length n are counted by C_n for n = 1 .. 8. -/
theorem busy_periods_are_catalan_1_8 :
    ∀ i : Fin 8,
      busyPeriodCount ((i : ℕ) + 1) = catalan ((i : ℕ) + 1) ∧
        busyPeriodCount ((i : ℕ) + 1) = busyPeriodTable i := by
  native_decide

/-! ## Ballot problem -/

/-- Strict ballot probability: candidate A is always ahead, with a > b. -/
def ballotProbability (a b : ℕ) : ℚ :=
  ((a : ℚ) - (b : ℚ)) / ((a : ℚ) + (b : ℚ))

theorem ballot_3_1 :
    ballotProbability 3 1 = 1 / 2 := by
  native_decide

theorem ballot_4_2 :
    ballotProbability 4 2 = 1 / 3 := by
  native_decide

theorem ballot_5_1 :
    ballotProbability 5 1 = 2 / 3 := by
  native_decide

theorem ballot_5_3 :
    ballotProbability 5 3 = 1 / 4 := by
  native_decide

/-! ## Cycle lemma form of Catalan numbers -/

/-- Cycle-lemma expression (1/(n+1)) * binom(2n,n), evaluated in rationals. -/
def cycleLemmaCatalan (n : ℕ) : ℚ :=
  (1 : ℚ) / ((n : ℚ) + 1) * (Nat.choose (2 * n) n : ℚ)

/-- The cycle-lemma expression agrees with Catalan numbers for n = 0 .. 8. -/
theorem cycle_lemma_catalan_0_8 :
    ∀ n : Fin 9, cycleLemmaCatalan (n : ℕ) = (catalan (n : ℕ) : ℚ) := by
  native_decide

/-! ## Erlang-B blocking formula -/

/-- Erlang-B summand rho^k/k!. -/
def erlangTerm (rho : ℚ) (k : ℕ) : ℚ :=
  rho ^ k / (Nat.factorial k : ℚ)

/-- Erlang-B denominator Σ_{k=0}^c rho^k/k!. -/
def erlangDenominator (rho : ℚ) (c : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (c + 1), erlangTerm rho k

/-- Erlang-B blocking probability: (rho^c/c!) / Σ_{k=0}^c rho^k/k!. -/
def erlangB (rho : ℚ) (c : ℕ) : ℚ :=
  erlangTerm rho c / erlangDenominator rho c

theorem erlang_b_c_two_rho_one :
    erlangB 1 2 = 1 / 5 := by
  native_decide

theorem erlang_b_c_two_rho_one_expanded :
    ((1 : ℚ) / 2) / (1 + 1 + (1 / 2)) = 1 / 5 := by
  native_decide

end QueueingAsymptotics
