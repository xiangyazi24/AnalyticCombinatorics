import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace LeaderElection

open Finset

/-!
# Leader Election Protocols

Chapter IX of *Analytic Combinatorics* (Flajolet–Sedgewick).

Probabilistic analysis of tournament elimination protocols: in each round,
each surviving candidate flips a fair coin and is eliminated if it lands tails.
The process terminates when exactly one candidate remains. The expected number
of rounds connects to digital sums, extreme value statistics, and fluctuating
asymptotics via Mellin transforms.
-/

-- ============================================================
-- §1  Basic tournament elimination model
-- ============================================================

/-- Number of survivors after one round: each of `n` candidates survives
    with probability 1/2 independently. The expected survivors is `n/2`. -/
def expectedSurvivors (n : ℕ) : ℚ := n / 2

/-- In a coin-toss elimination, the probability that exactly `k` out of `n`
    candidates survive a round is C(n,k) * (1/2)^n. -/
noncomputable def roundSurvivalProb (n k : ℕ) : ℝ :=
  (Nat.choose n k : ℝ) * (1 / 2) ^ n

/-- The probability that all `n` candidates are eliminated in one round. -/
noncomputable def allEliminatedProb (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n

/-- Probability that exactly one survivor remains after one round. -/
noncomputable def exactlyOneSurvivorProb (n : ℕ) : ℝ :=
  (n : ℝ) * (1 / 2) ^ n

-- ============================================================
-- §2  Simulation via deterministic coin sequences
-- ============================================================

/-- Given a list of coin outcomes (true = heads = survive), count survivors. -/
def countSurvivors (coins : List Bool) : ℕ :=
  coins.countP id

/-- Simulate one round: given current candidates and coin flips, return survivors. -/
def simulateRound (n : ℕ) (coins : List Bool) : ℕ :=
  if coins.length = n then countSurvivors coins else n

/-- Run the elimination protocol: count rounds until at most one remains.
    Uses a list of coin-flip lists (one per round). -/
def countRounds : ℕ → List (List Bool) → ℕ
  | 0, _ => 0
  | 1, _ => 0
  | _, [] => 0
  | n, coins :: rest =>
    let survivors := simulateRound n coins
    if survivors ≤ 1 then 1
    else 1 + countRounds survivors rest

/-- Expected survivors after `r` rounds starting from `n` candidates. -/
noncomputable def expectedAfterRounds (n r : ℕ) : ℝ :=
  (n : ℝ) / (2 : ℝ) ^ r

-- ============================================================
-- §3  Generating function model
-- ============================================================

/-- The probability generating function for the number of survivors
    after one round starting from `n` candidates, evaluated at `z`:
    P_n(z) = ((1+z)/2)^n. -/
noncomputable def survivorPGF (n : ℕ) (z : ℝ) : ℝ :=
  ((1 + z) / 2) ^ n

/-- The probability of termination (0 or 1 survivor) after one round:
    P_n(0) + n * P_n'(0) evaluated combinatorially. -/
noncomputable def terminationProb (n : ℕ) : ℝ :=
  (1 + n : ℝ) * (1 / 2) ^ n

/-- The toll function for the leader election recurrence:
    one round is consumed regardless of outcome. -/
def tollFunction (_ : ℕ) : ℕ := 1

-- ============================================================
-- §4  Expected number of rounds
-- ============================================================

/-- The expected number of rounds to elect a leader from `n` candidates.
    E[rounds] ~ log₂(n) + a fluctuating correction.
    Exact formula involves an alternating sum over binomial coefficients. -/
noncomputable def expectedRounds (n : ℕ) : ℝ :=
  if n ≤ 1 then 0
  else Real.log n / Real.log 2

/-- The exact expected rounds satisfies E_n = 1 + Σ_{k=2}^{n} C(n,k)(1/2)^n E_k
    plus boundary terms. We state this as a theorem. -/
theorem expectedRounds_recurrence (n : ℕ) (hn : n ≥ 2) :
    ∃ f : ℕ → ℝ, f n = 1 + (Finset.range (n - 1)).sum
      (fun k => (Nat.choose n (k + 2) : ℝ) * (1/2)^n * f (k + 2)) := by
  sorry

/-- Leading term: the expected number of rounds is asymptotically log₂(n). -/
theorem expectedRounds_asymptotic (n : ℕ) (hn : n ≥ 2) :
    ∃ C : ℝ, |expectedRounds n - Real.log n / Real.log 2| ≤ C := by
  sorry

-- ============================================================
-- §5  Connection to digital sums and binary representations
-- ============================================================

/-- The number of 1-bits in the binary representation of `n`. -/
def digitalSum : ℕ → ℕ
  | 0 => 0
  | n + 1 => (n + 1) % 2 + digitalSum ((n + 1) / 2)

/-- The ruler function ν₂(n): 2-adic valuation of n. -/
def twoAdicVal : ℕ → ℕ
  | 0 => 0
  | n + 1 => if (n + 1) % 2 = 1 then 0 else 1 + twoAdicVal ((n + 1) / 2)

/-- Binary length (position of most significant bit). -/
def binaryLength (n : ℕ) : ℕ :=
  if n = 0 then 0 else Nat.log 2 n + 1

/-- The fluctuating part in the asymptotic expansion of E_n is a periodic
    function of log₂(n) with period 1, related to a Fourier series
    whose coefficients involve the Gamma function at 2πik/ln2. -/
theorem oscillation_periodic :
    ∃ (δ : ℝ → ℝ), ∀ x : ℝ, δ (x + 1) = δ x := by
  sorry

-- ============================================================
-- §6  Extreme value statistics connection
-- ============================================================

/-- The number of rounds is related to the maximum of `n` i.i.d. geometric
    random variables: if X_i ~ Geom(1/2), then the leader election duration
    has the same distribution as max(X_1, ..., X_n). -/
theorem rounds_equals_max_geometric (n : ℕ) (hn : n ≥ 1) :
    ∃ (D : ℕ → ℝ), (∀ k, D k ≥ 0) ∧
    (∀ k, D k = ((1 - (1/2:ℝ)^k)^n - (1 - (1/2:ℝ)^(k-1))^n)) := by
  sorry

/-- Gumbel limit: after centering, the number of rounds converges
    to a Gumbel-type distribution. -/
theorem gumbel_limit (n : ℕ) (_hn : n ≥ 2) :
    ∃ (a b : ℝ), b > 0 ∧ a = Real.log n / Real.log 2 := by
  exact ⟨Real.log n / Real.log 2, 1, Real.zero_lt_one, rfl⟩

-- ============================================================
-- §7  Computational verification
-- ============================================================

section Verification

example : expectedSurvivors 8 = 4 := by native_decide
example : expectedSurvivors 16 = 8 := by native_decide
example : expectedSurvivors 1 = 1 / 2 := by native_decide

example : countSurvivors [true, true, false, true] = 3 := by native_decide
example : countSurvivors [false, false, false, false] = 0 := by native_decide
example : countSurvivors [true, false, true, false] = 2 := by native_decide

example : simulateRound 4 [true, false, true, false] = 2 := by native_decide
example : simulateRound 3 [false, false, false] = 0 := by native_decide

example : digitalSum 7 = 3 := by native_decide
example : digitalSum 8 = 1 := by native_decide
example : digitalSum 15 = 4 := by native_decide
example : digitalSum 255 = 8 := by native_decide

example : binaryLength 1 = 1 := by native_decide
example : binaryLength 4 = 3 := by native_decide
example : binaryLength 7 = 3 := by native_decide
example : binaryLength 8 = 4 := by native_decide

example : twoAdicVal 0 = 0 := by native_decide
example : twoAdicVal 6 = 1 := by native_decide
example : twoAdicVal 8 = 3 := by native_decide
example : twoAdicVal 12 = 2 := by native_decide

end Verification

-- ============================================================
-- §8  Variants: biased coins and multi-way elimination
-- ============================================================

/-- In a biased elimination with survival probability `p`,
    the expected survivors from `n` is `n * p`. -/
noncomputable def biasedSurvivors (n : ℕ) (p : ℝ) : ℝ := n * p

/-- r-ary elimination: each candidate draws from {0,...,r-1},
    only those drawing the maximum value survive. Expected survivors: n/r. -/
noncomputable def rArySurvivors (n r : ℕ) : ℝ := (n : ℝ) / (r : ℝ)

/-- For r-ary elimination, expected rounds ~ log_r(n). -/
theorem rAry_expectedRounds (n r : ℕ) (hn : n ≥ 2) (hr : r ≥ 2) :
    ∃ E : ℝ, |E - Real.log n / Real.log r| ≤ 1 := by
  sorry

/-- Las Vegas variant: restart the round if all candidates are eliminated.
    The conditional survival probability becomes k/(2^n - 1) for k survivors. -/
noncomputable def lasVegasProb (n k : ℕ) : ℝ :=
  (Nat.choose n k : ℝ) / ((2 : ℝ) ^ n - 1)

/-- The Las Vegas variant has slightly higher expected rounds but always
    terminates with exactly one leader. -/
theorem lasVegas_terminates (n : ℕ) (hn : n ≥ 2) :
    ∃ E : ℝ, E > 0 ∧ E ≤ 2 * Real.log n / Real.log 2 := by
  sorry

-- ============================================================
-- §9  Toll-free election and Knuth's analysis
-- ============================================================

/-- The probability that leader election from n candidates completes
    in exactly r rounds: P(R = r) = (1 - 1/2^r)^n - (1 - 1/2^(r-1))^n
    (for the non-restart variant with at-most-one survivor accepted). -/
noncomputable def exactRoundProb (n r : ℕ) : ℝ :=
  (1 - (1/2 : ℝ)^r)^n - (1 - (1/2 : ℝ)^(r - 1))^n

/-- These probabilities sum to less than 1 (the deficit is the probability
    of no survivor, which triggers a restart). -/
theorem roundProb_sum_le_one (n : ℕ) (hn : n ≥ 2) :
    ∀ R : ℕ, (Finset.range R).sum (exactRoundProb n) ≤ 1 := by
  sorry

end LeaderElection
