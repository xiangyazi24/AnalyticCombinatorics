import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace SteepestDescent

/-!
  Chapter V: steepest descent and stationary phase.

  The analytic statements are recorded as executable numerical certificates:

  * Stirling from the Gaussian saddle:
    `n! ~ sqrt(2*pi*n) * (n/e)^n`.
  * Stirling log remainder:
    `1/(12*n+1) < log(n!) - (n+1/2)*log n + n - log(sqrt(2*pi)) < 1/(12*n)`.
  * Laplace method:
    `integral exp(-n*f(x)) dx ~ sqrt(2*pi/(n*f''(x0))) * exp(-n*f(x0))`.
  * Central binomial and Catalan saddle estimates:
    `choose (2*n) n ~ 4^n / sqrt(pi*n)` and
    `Catalan n ~ 4^n / (n^(3/2) * sqrt(pi))`.

  Since `native_decide` cannot evaluate real square roots, exponentials, logs,
  or integrals, the tables below store integer floors of the corresponding
  real quantities after a fixed decimal scaling.  The proofs verify the
  displayed ranges, ratios, and monotonicity properties by computation.
-/

/-- Lookup in a finite natural-number table, extended by zero. -/
def tableNat {N : ℕ} (a : Fin N → ℕ) (n : ℕ) : ℕ :=
  if h : n < N then a ⟨n, h⟩ else 0

/-- `n!` for `n=1..8`, paired with the Stirling decimal table. -/
def factorial1To8 : Fin 8 → ℕ := ![1, 2, 6, 24, 120, 720, 5040, 40320]

theorem factorial1To8_correct :
    ∀ i : Fin 8, factorial1To8 i = Nat.factorial ((i : ℕ) + 1) := by
  native_decide

/-! ## Gaussian saddle for factorials -/

/--
`floor(10000 * sqrt(2*pi*n) * (n/e)^n)` for `n=1..8`.

Thus the displayed decimal comparison is this table divided by `10000`:
`0.9221, 1.9190, 5.8362, 23.5061, 118.0191, 710.0781,
4980.3958, 39902.3954`, compared with `1!,...,8!`.
-/
def stirlingScaled10000 : Fin 8 → ℕ :=
  ![9221, 19190, 58362, 235061, 1180191, 7100781, 49803958, 399023954]

theorem stirlingScaled10000_below_factorials :
    ∀ i : Fin 8, stirlingScaled10000 i < 10000 * factorial1To8 i := by
  native_decide

theorem stirlingScaled10000_close_to_factorials :
    ∀ i : Fin 8, 9000 * factorial1To8 i < stirlingScaled10000 i := by
  native_decide

/--
`floor(1000000 * sqrt(2*pi*n) * (n/e)^n) / n!` for `n=1..12`.
The increasing values are the floor ratios behind the Gaussian approximation.
-/
def stirlingRatioPerMillion : Fin 12 → ℕ :=
  ![922137, 959502, 972701, 979423, 983493, 986219,
    988173, 989642, 990787, 991704, 992454, 993081]

theorem stirling_floor_ratios_increase :
    ∀ i : Fin 11,
      tableNat stirlingRatioPerMillion (i : ℕ) <
        tableNat stirlingRatioPerMillion ((i : ℕ) + 1) := by
  native_decide

theorem stirling_floor_ratios_are_subunit :
    ∀ i : Fin 12, stirlingRatioPerMillion i < 1000000 := by
  native_decide

/-! ## Stirling log-remainder bounds -/

/--
`floor(10^9 * R_n)` for `n=1..12`, where
`R_n = log(n!) - (n+1/2)*log n + n - log(sqrt(2*pi))`.
-/
def stirlingLogRemainderPerBillion : Fin 12 → ℕ :=
  ![81061466, 41340695, 27677925, 20790672, 16644691, 13876128,
    11896709, 10411265, 9255462, 8330563, 7573675, 6942840]

/--
Integerized form of
`1/(12*n+1) < R_n < 1/(12*n)` for `n=1..12`, with scale `10^9`.
-/
theorem stirling_log_remainder_bounds :
    ∀ i : Fin 12,
      let n := (i : ℕ) + 1
      1000000000 < stirlingLogRemainderPerBillion i * (12 * n + 1) ∧
        stirlingLogRemainderPerBillion i * (12 * n) < 1000000000 := by
  native_decide

/-! ## Relative quality of the unscaled Stirling floor -/

/-- `floor(sqrt(2*pi*n) * (n/e)^n)` for `n=1..15`. -/
def stirlingFloor1To15 : Fin 15 → ℕ :=
  ![0, 1, 5, 23, 118, 710, 4980, 39902, 359536, 3598695,
    39615625, 475687486, 6187239475, 86661001740, 1300430722199]

/-- The absolute error `n! - floor(sqrt(2*pi*n) * (n/e)^n)` for `n=1..15`. -/
def stirlingFloorError1To15 : Fin 15 → ℕ :=
  ![1, 1, 1, 1, 2, 10, 60, 418, 3344, 30105,
    301175, 3314114, 39781325, 517289460, 7243645801]

theorem stirling_floor_error_table_correct :
    ∀ i : Fin 15,
      stirlingFloorError1To15 i =
        Nat.factorial ((i : ℕ) + 1) - stirlingFloor1To15 i := by
  native_decide

/--
`|n! - floor(sqrt(2*pi*n)*(n/e)^n)| / n!` decreases for `n=1..15`.
-/
theorem stirling_floor_relative_error_decreases :
    ∀ i : Fin 14,
      tableNat stirlingFloorError1To15 ((i : ℕ) + 1) *
          Nat.factorial ((i : ℕ) + 1) <
        tableNat stirlingFloorError1To15 (i : ℕ) *
          Nat.factorial ((i : ℕ) + 2) := by
  native_decide

/-! ## Laplace method and saddle-point integral checks -/

/--
For `f(x)=x^2`, `x0=0`, and `f''(x0)=2`, Laplace gives
`integral exp(-n*x^2) dx = sqrt(pi/n)`.  This table stores
`floor(10000 * sqrt(pi/n))` for `n=1..8`.
-/
def gaussianIntegralScaled10000 : Fin 8 → ℕ :=
  ![17724, 12533, 10233, 8862, 7926, 7236, 6699, 6266]

theorem gaussian_integral_laplace_values_decrease :
    ∀ i : Fin 7,
      tableNat gaussianIntegralScaled10000 ((i : ℕ) + 1) <
        tableNat gaussianIntegralScaled10000 (i : ℕ) := by
  native_decide

/--
Saddle-point coefficient integral estimate
`choose (2*n) n ≈ 4^n / sqrt(pi*n)`.
This table is `floor(1000 * 4^n / sqrt(pi*n))` for `n=1..10`.
-/
def saddleCentralApproxPerThousand : Fin 10 → ℕ :=
  ![2256, 6383, 20847, 72216, 258368, 943429, 3493783,
    13072540, 49299638, 187078972]

theorem saddle_integer_approximations_track_central_binomial :
    ∀ i : Fin 10,
      let n := (i : ℕ) + 1
      1000 * Nat.choose (2 * n) n < saddleCentralApproxPerThousand i ∧
        saddleCentralApproxPerThousand i < 1150 * Nat.choose (2 * n) n := by
  native_decide

/-! ## Central binomial saddle ratio -/

/--
`floor(1000 * choose(2*n,n) * sqrt(pi*n) / 4^n)` for `n=1..10`.
These values check the ratio to the asymptotic `4^n / sqrt(pi*n)`.
-/
def centralBinomialRatioPerThousand : Fin 10 → ℕ :=
  ![886, 939, 959, 969, 975, 979, 982, 984, 986, 987]

theorem central_binomial_ratio_increases :
    ∀ i : Fin 9,
      tableNat centralBinomialRatioPerThousand (i : ℕ) <
        tableNat centralBinomialRatioPerThousand ((i : ℕ) + 1) := by
  native_decide

theorem central_binomial_ratio_close_to_one :
    ∀ i : Fin 10, 880 < centralBinomialRatioPerThousand i ∧
      centralBinomialRatioPerThousand i < 1000 := by
  native_decide

theorem central_binomial_values_1_to_10 :
    (∀ i : Fin 10,
      let n := (i : ℕ) + 1
      Nat.choose (2 * n) n =
        tableNat (![2, 6, 20, 70, 252, 924, 3432, 12870, 48620, 184756] : Fin 10 → ℕ)
          (i : ℕ)) := by
  native_decide

/-! ## Catalan saddle ratio -/

/-- The Catalan number `C_n = choose(2*n,n)/(n+1)`. -/
def catalanNum (n : ℕ) : ℕ :=
  Nat.choose (2 * n) n / (n + 1)

/--
`floor(1000 * C_n * n^(3/2) * sqrt(pi) / 4^n)` for `n=1..10`.
These values check `C_n ~ 4^n / (n^(3/2) * sqrt(pi))`.
-/
def catalanRatioPerThousand : Fin 10 → ℕ :=
  ![443, 626, 719, 775, 812, 839, 859, 875, 887, 897]

theorem catalan_values_1_to_10 :
    (∀ i : Fin 10,
      let n := (i : ℕ) + 1
      catalanNum n =
        tableNat (![1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796] : Fin 10 → ℕ)
          (i : ℕ)) := by
  native_decide

theorem catalan_asymptotic_ratio_increases :
    ∀ i : Fin 9,
      tableNat catalanRatioPerThousand (i : ℕ) <
        tableNat catalanRatioPerThousand ((i : ℕ) + 1) := by
  native_decide

theorem catalan_asymptotic_ratio_bounds :
    ∀ i : Fin 10, 400 < catalanRatioPerThousand i ∧
      catalanRatioPerThousand i < 1000 := by
  native_decide

end SteepestDescent
