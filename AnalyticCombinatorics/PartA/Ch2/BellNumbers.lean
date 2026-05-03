import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace BellNumbers

open Finset BigOperators

/-! ## Stirling Numbers of the Second Kind -/

/-- Stirling numbers of the second kind S(n, k): the number of partitions
    of an n-element set into exactly k non-empty blocks. -/
def stirling2 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => stirling2 n k + (k + 1) * stirling2 n (k + 1)

theorem stirling2_zero_zero : stirling2 0 0 = 1 := by native_decide
theorem stirling2_n_zero (n : ℕ) (hn : 0 < n) : stirling2 n 0 = 0 := by
  cases n with | zero => omega | succ n => rfl

theorem stirling2_n_one (n : ℕ) (hn : 0 < n) : stirling2 n 1 = 1 := by
  sorry

theorem stirling2_n_n (n : ℕ) : stirling2 n n = 1 := by
  sorry

theorem stirling2_recurrence (n k : ℕ) :
    stirling2 (n + 1) (k + 1) = stirling2 n k + (k + 1) * stirling2 n (k + 1) := by
  rfl

/-! ## Bell Numbers via Recurrence -/

/-- Bell numbers B(n): the total number of partitions of an n-element set,
    defined by the binomial recurrence B(n+1) = ∑_{k=0}^{n} C(n,k) B(k). -/
def bell : ℕ → ℕ
  | 0 => 1
  | n + 1 => ∑ k ∈ (range (n + 1)).attach, Nat.choose n k.val * bell k.val
termination_by n => n
decreasing_by exact Nat.lt_succ_iff.mp (Nat.succ_lt_succ (mem_range.mp k.2))

/-- The Bell recurrence in standard summation form. -/
theorem bell_recurrence (n : ℕ) :
    bell (n + 1) = ∑ k ∈ range (n + 1), Nat.choose n k * bell k := by
  rw [bell]
  exact sum_attach (range (n + 1)) fun k => Nat.choose n k * bell k

/-! ## Numerical Sanity Checks -/

theorem bell_zero : bell 0 = 1 := by native_decide
theorem bell_one : bell 1 = 1 := by native_decide
theorem bell_two : bell 2 = 2 := by native_decide
theorem bell_three : bell 3 = 5 := by native_decide
theorem bell_four : bell 4 = 15 := by native_decide
theorem bell_five : bell 5 = 52 := by native_decide
theorem bell_six : bell 6 = 203 := by native_decide
theorem bell_seven : bell 7 = 877 := by native_decide

/-! ## Bell Numbers as Stirling Row Sums -/

/-- B(n) = ∑_{k=0}^{n} S(n, k), the connection to set partitions. -/
theorem bell_eq_sum_stirling2 (n : ℕ) :
    bell n = ∑ k ∈ range (n + 1), stirling2 n k := by
  sorry

theorem bell_eq_sum_stirling2_check (n : ℕ) (hn : n ≤ 7) :
    bell n = ∑ k ∈ range (n + 1), stirling2 n k := by
  interval_cases n <;> native_decide

/-! ## Dobinski's Formula -/

/-- Dobinski's formula partial sum: ∑_{k=0}^{N} k^n / k!.
    The full Dobinski formula states B(n) = (1/e) ∑_{k≥0} k^n / k!. -/
noncomputable def dobinskiPartialSum (n N : ℕ) : ℝ :=
  ∑ k ∈ range (N + 1), (k ^ n : ℝ) / (Nat.factorial k : ℝ)

/-- Dobinski's formula: B(n) = (1/e) · ∑_{k=0}^{∞} k^n / k!. -/
theorem dobinski_formula (n : ℕ) :
    (bell n : ℝ) = Real.exp (-1) *
      ∑' (k : ℕ), (k ^ n : ℝ) / (Nat.factorial k : ℝ) := by
  sorry

/-- The Dobinski series converges absolutely for every n. -/
theorem dobinski_summable (n : ℕ) :
    Summable (fun k : ℕ => (k ^ n : ℝ) / (Nat.factorial k : ℝ)) := by
  sorry

/-! ## Exponential Generating Function -/

/-- The exponential generating function of Bell numbers:
    ∑_{n≥0} B(n) x^n / n! = exp(e^x - 1).
    We state this as a formal power series identity. -/
noncomputable def bellEGFCoeff (n : ℕ) : ℝ :=
  (bell n : ℝ) / (Nat.factorial n : ℝ)

/-- The EGF identity: ∑ B(n) x^n / n! = exp(exp(x) - 1). -/
theorem bell_egf_is_exp_exp_minus_one :
    ∀ (x : ℝ), ∑' (n : ℕ), bellEGFCoeff n * x ^ n =
      Real.exp (Real.exp x - 1) := by
  sorry

/-- EGF convergence: the series ∑ B(n) x^n / n! converges for all x ∈ ℝ. -/
theorem bell_egf_converges (x : ℝ) :
    Summable (fun n : ℕ => bellEGFCoeff n * x ^ n) := by
  sorry

/-! ## Bell Polynomial Recurrence (Bell Triangle) -/

/-- The Bell triangle: a_{i,j} where a_{0,0} = 1 and each row starts
    with the last element of the previous row. Bell numbers appear
    as the first element of each row. -/
def bellTriangle : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, 0 => bellTriangle n n
  | n + 1, k + 1 => bellTriangle (n + 1) k + bellTriangle n k

theorem bellTriangle_row_start (n : ℕ) :
    bellTriangle (n + 1) 0 = bellTriangle n n := by
  simp [bellTriangle]

theorem bellTriangle_gives_bell (n : ℕ) :
    bellTriangle n 0 = bell n := by
  sorry

theorem bellTriangle_check : bellTriangle 4 0 = 15 := by native_decide
theorem bellTriangle_check2 : bellTriangle 5 0 = 52 := by native_decide
theorem bellTriangle_check3 : bellTriangle 6 0 = 203 := by native_decide

/-! ## Growth and Monotonicity -/

theorem bell_pos (n : ℕ) : 0 < bell n := by
  sorry

theorem bell_monotone (n : ℕ) : bell n ≤ bell (n + 1) := by
  sorry

theorem bell_strict_mono (n : ℕ) (hn : 1 ≤ n) : bell n < bell (n + 1) := by
  sorry

/-! ## Asymptotic Growth Rate -/

/-- The asymptotic growth of Bell numbers: log B(n) ~ n log n - n log log n.
    More precisely, B(n) ~ (1/√n) · (n / (W(n)))^n · exp(n/W(n) - 1)
    where W is the Lambert W function. We state the weaker superexponential bound. -/
theorem bell_superexponential_growth :
    ∀ C : ℝ, 0 < C → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → C ^ n < (bell n : ℝ) := by
  sorry

/-- Bell numbers grow faster than n! eventually. -/
theorem bell_exceeds_factorial :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Nat.factorial n ≤ bell n := by
  sorry

/-! ## Surjection Counting -/

/-- The number of surjections from an n-set to a k-set equals k! · S(n, k). -/
def surjectionCount (n k : ℕ) : ℕ :=
  Nat.factorial k * stirling2 n k

theorem surjection_count_check :
    surjectionCount 4 2 = 14 := by native_decide

theorem surjection_count_check2 :
    surjectionCount 4 3 = 36 := by native_decide

/-- The total number of functions from [n] to [n] that are surjective. -/
theorem surjection_n_n (n : ℕ) (hn : 0 < n) :
    surjectionCount n n = Nat.factorial n := by
  sorry

/-! ## Set Partition Interpretation -/

/-- Bell numbers count the number of equivalence relations on a finite set. -/
theorem bell_counts_equivalence_relations (n : ℕ) :
    bell n = ∑ k ∈ range (n + 1), stirling2 n k := by
  exact bell_eq_sum_stirling2 n

/-- The exponential formula: the EGF of set partitions factors through
    the EGF of connected components (singleton blocks have EGF e^x - 1),
    giving the overall EGF exp(e^x - 1).
    We verify the first few EGF coefficients B(n)/n! match. -/
theorem bell_exponential_formula_interpretation :
    bellEGFCoeff 0 = 1 ∧ bellEGFCoeff 1 = 1 := by
  sorry

/-! ## Convexity of Log Bell Numbers -/

/-- The sequence log B(n) is convex: B(n)^2 ≤ B(n-1) · B(n+1). -/
theorem bell_log_convexity (n : ℕ) (hn : 1 ≤ n) :
    bell n * bell n ≤ bell (n - 1) * bell (n + 1) := by
  sorry

theorem bell_log_convexity_check :
    bell 2 * bell 2 ≤ bell 1 * bell 3 := by native_decide

theorem bell_log_convexity_check2 :
    bell 3 * bell 3 ≤ bell 2 * bell 4 := by native_decide

theorem bell_log_convexity_check3 :
    bell 4 * bell 4 ≤ bell 3 * bell 5 := by native_decide

end BellNumbers
