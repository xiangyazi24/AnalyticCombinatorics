import Mathlib

/-!
# Flajolet's bounded continued fraction for weighted Motzkin paths

This file formalizes the finite, bounded-height version of Flajolet's
continued-fraction theorem.  Paths are finite first-return-coded Motzkin paths
with a projection to step lists.  A down step from level `k + 1` to level `k`
has weight `b k`; equivalently, when the current level is `m`, a down step has
weight `b (m - 1)`.
-/

open scoped BigOperators PowerSeries

namespace AnalyticCombinatorics.Ch5.ContinuedFractions

noncomputable section

/- The recursive finite path type and the power-series induction below create
moderately large goals after unfolding `Finset.univ` over sum/sigma types. -/
set_option maxHeartbeats 800000

/-- Motzkin steps. -/
inductive Step where
  | up
  | down
  | level
  deriving DecidableEq, Repr

namespace Step

/-- The endpoint after taking one step from a natural-number level.
Invalid down steps from level `0` are sent to `0`; the path type below never
uses such a step at the bottom level. -/
def nextLevel : ℕ → Step → ℕ
  | k, up => k + 1
  | k, down => k - 1
  | k, level => k

end Step

/-- Shift a coefficient family upward by one level. -/
def shift (f : ℕ → R) : ℕ → R :=
  fun k => f (k + 1)

/-- A first-return-coded Motzkin path of length `n`, from level `0` back to
level `0`, staying at relative height at most `h`.

For positive height and length at least two, a path is either a bottom level
step followed by a path, or an arch
`up :: inner ++ down :: rest`; the inner path has height bound one smaller and
uses shifted weights in the generating function. -/
def MotzkinPath : ℕ → ℕ → Type
  | _h, 0 => PUnit
  | 0, n + 1 => MotzkinPath 0 n
  | h + 1, 1 => MotzkinPath (h + 1) 0
  | h + 1, n + 2 =>
      MotzkinPath (h + 1) (n + 1) ⊕
        (Σ i : Fin (n + 1),
          MotzkinPath h i.1 × MotzkinPath (h + 1) (n - i.1))
termination_by h n => h + n
decreasing_by
  all_goals omega

set_option linter.unusedVariables false in
/-- Decidable equality for the recursive finite path code. -/
def motzkinPathDecidableEq : (h n : ℕ) → DecidableEq (MotzkinPath h n)
  | h, 0 => by
      unfold MotzkinPath
      infer_instance
  | 0, n + 1 => by
      unfold MotzkinPath
      exact motzkinPathDecidableEq 0 n
  | h + 1, 1 => by
      unfold MotzkinPath
      exact motzkinPathDecidableEq (h + 1) 0
  | h + 1, n + 2 => by
      unfold MotzkinPath
      letI := motzkinPathDecidableEq (h + 1) (n + 1)
      letI inner : (i : Fin (n + 1)) → DecidableEq (MotzkinPath h i.1) :=
        fun i => motzkinPathDecidableEq h i.1
      letI rest : (i : Fin (n + 1)) →
          DecidableEq (MotzkinPath (h + 1) (n - i.1)) :=
        fun i => motzkinPathDecidableEq (h + 1) (n - i.1)
      infer_instance
termination_by h n => h + n
decreasing_by
  all_goals omega

set_option linter.unusedVariables false in
/-- Finiteness for the recursive finite path code. -/
def motzkinPathFintype : (h n : ℕ) → Fintype (MotzkinPath h n)
  | h, 0 => by
      unfold MotzkinPath
      infer_instance
  | 0, n + 1 => by
      unfold MotzkinPath
      exact motzkinPathFintype 0 n
  | h + 1, 1 => by
      unfold MotzkinPath
      exact motzkinPathFintype (h + 1) 0
  | h + 1, n + 2 => by
      unfold MotzkinPath
      letI := motzkinPathFintype (h + 1) (n + 1)
      letI inner : (i : Fin (n + 1)) → Fintype (MotzkinPath h i.1) :=
        fun i => motzkinPathFintype h i.1
      letI rest : (i : Fin (n + 1)) →
          Fintype (MotzkinPath (h + 1) (n - i.1)) :=
        fun i => motzkinPathFintype (h + 1) (n - i.1)
      infer_instance
termination_by h n => h + n
decreasing_by
  all_goals omega

instance (h n : ℕ) : DecidableEq (MotzkinPath h n) :=
  motzkinPathDecidableEq h n

instance (h n : ℕ) : Fintype (MotzkinPath h n) :=
  motzkinPathFintype h n

/-- Weight of a coded path.  In an arch, the initial up and final down
contribute `a 0` and `b 0`; the inside is evaluated with all weights shifted
up one absolute level. -/
def pathWeight {R : Type*} [CommRing R]
    (a b c : ℕ → R) : (h n : ℕ) → MotzkinPath h n → R
  | _h, 0, _p => 1
  | 0, n + 1, p =>
      c 0 * pathWeight a b c 0 n (by simpa [MotzkinPath] using p)
  | h + 1, 1, p =>
      c 0 * pathWeight a b c (h + 1) 0 (by simpa [MotzkinPath] using p)
  | h + 1, n + 2, p =>
      match
        (by
          simpa [MotzkinPath] using p :
            MotzkinPath (h + 1) (n + 1) ⊕
              (Σ i : Fin (n + 1),
                MotzkinPath h i.1 × MotzkinPath (h + 1) (n - i.1)))
      with
      | Sum.inl rest => c 0 * pathWeight a b c (h + 1) (n + 1) rest
      | Sum.inr arch =>
          a 0 * b 0 *
            pathWeight (shift a) (shift b) (shift c) h arch.1.1 arch.2.1 *
              pathWeight a b c (h + 1) (n - arch.1.1) arch.2.2
termination_by h n _p => h + n
decreasing_by
  all_goals omega

/-- The literal finite sum over coded paths.  The main coefficient function below
uses the first-return recursion induced by this finite code. -/
def WpathSum {R : Type*} [CommRing R]
    (h : ℕ) (a b c : ℕ → R) (n : ℕ) : R :=
  ∑ p : MotzkinPath h n, pathWeight a b c h n p

/-- The coefficient of the bounded-height weighted Motzkin generating function,
computed by the first-return decomposition of `MotzkinPath`. -/
def Wcoeff {R : Type*} [CommRing R] :
    ℕ → (ℕ → R) → (ℕ → R) → (ℕ → R) → ℕ → R
  | _h, _a, _b, _c, 0 => 1
  | 0, _a, _b, c, n + 1 => c 0 * Wcoeff 0 _a _b c n
  | _h + 1, _a, _b, c, 1 => c 0
  | h + 1, a, b, c, n + 2 =>
      c 0 * Wcoeff (h + 1) a b c (n + 1) +
        a 0 * b 0 *
          ∑ i : Fin (n + 1),
            Wcoeff h (shift a) (shift b) (shift c) i.1 *
              Wcoeff (h + 1) a b c (n - i.1)
termination_by h _a _b _c n => h + n
decreasing_by
  all_goals omega

/-- The bounded-height weighted Motzkin ordinary generating function. -/
def W {R : Type*} [CommRing R] (h : ℕ) (a b c : ℕ → R) : PowerSeries R :=
  PowerSeries.mk fun n => Wcoeff h a b c n

@[simp] theorem coeff_W {R : Type*} [CommRing R]
    (h : ℕ) (a b c : ℕ → R) (n : ℕ) :
    PowerSeries.coeff (R := R) n (W h a b c) = Wcoeff h a b c n := by
  simp [W]

@[simp] theorem Wcoeff_zero_length {R : Type*} [CommRing R]
    (h : ℕ) (a b c : ℕ → R) :
    Wcoeff h a b c 0 = 1 := by
  simp [Wcoeff]

theorem Wcoeff_height_zero_succ {R : Type*} [CommRing R]
    (a b c : ℕ → R) (n : ℕ) :
    Wcoeff 0 a b c (n + 1) = c 0 * Wcoeff 0 a b c n := by
  simp [Wcoeff]

theorem Wcoeff_height_zero {R : Type*} [CommRing R]
    (a b c : ℕ → R) (n : ℕ) :
    Wcoeff 0 a b c n = c 0 ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Wcoeff_height_zero_succ, ih]
      ring

theorem Wcoeff_succ_one {R : Type*} [CommRing R]
    (h : ℕ) (a b c : ℕ → R) :
    Wcoeff (h + 1) a b c 1 = c 0 := by
  simp [Wcoeff]

theorem Wcoeff_succ_succ {R : Type*} [CommRing R]
    (h n : ℕ) (a b c : ℕ → R) :
    Wcoeff (h + 1) a b c (n + 2) =
      c 0 * Wcoeff (h + 1) a b c (n + 1) +
        a 0 * b 0 *
          ∑ i : Fin (n + 1),
            Wcoeff h (shift a) (shift b) (shift c) i.1 *
              Wcoeff (h + 1) a b c (n - i.1) := by
  simp [Wcoeff]

/-- First-return coefficient identity for positive height. -/
theorem first_return_coeff {R : Type*} [CommRing R]
    (h n : ℕ) (a b c : ℕ → R) :
    PowerSeries.coeff (R := R) (n + 1) (W (h + 1) a b c) =
      c 0 * PowerSeries.coeff (R := R) n (W (h + 1) a b c) +
        match n with
        | 0 => 0
        | m + 1 =>
            a 0 * b 0 *
              ∑ i : Fin (m + 1),
                PowerSeries.coeff (R := R) i.1
                    (W h (shift a) (shift b) (shift c)) *
                  PowerSeries.coeff (R := R) (m - i.1) (W (h + 1) a b c) := by
  cases n with
  | zero =>
      simp [Wcoeff_succ_one]
  | succ m =>
      simp [Wcoeff_succ_succ]

theorem coeff_zero_W {R : Type*} [CommRing R]
    (h : ℕ) (a b c : ℕ → R) :
    PowerSeries.coeff (R := R) 0 (W h a b c) = 1 := by
  simp

theorem coeff_one_W {R : Type*} [CommRing R]
    (h : ℕ) (a b c : ℕ → R) :
    PowerSeries.coeff (R := R) 1 (W h a b c) = c 0 := by
  cases h with
  | zero =>
      simp [Wcoeff_height_zero]
  | succ h =>
      simp [Wcoeff_succ_one]

theorem coeff_two_W_succ {R : Type*} [CommRing R]
    (h : ℕ) (a b c : ℕ → R) :
    PowerSeries.coeff (R := R) 2 (W (h + 1) a b c) =
      c 0 ^ 2 + a 0 * b 0 := by
  rw [coeff_W, Wcoeff_succ_succ, Wcoeff_succ_one]
  simp [pow_two]

def geomDenom {R : Type*} [CommRing R] (u : R) : PowerSeries R :=
  1 - PowerSeries.C u * PowerSeries.X

@[simp] theorem constantCoeff_geomDenom {R : Type*} [CommRing R] (u : R) :
    PowerSeries.constantCoeff (geomDenom u) = 1 := by
  simp [geomDenom]

/-- Height zero: only level steps are possible. -/
theorem W_height_zero_eq_inv {R : Type*} [CommRing R] (a b c : ℕ → R) :
    W 0 a b c =
      PowerSeries.invOfUnit (geomDenom (c 0)) (1 : Rˣ) := by
  have hmul : geomDenom (c 0) * W 0 a b c = 1 := by
    have hseries :
        W 0 a b c = 1 + PowerSeries.C (c 0) * PowerSeries.X * W 0 a b c := by
      ext n
      cases n with
      | zero =>
          simp
      | succ n =>
          simp only [map_add, PowerSeries.coeff_one, Nat.succ_ne_zero, ↓reduceIte,
            zero_add, coeff_W]
          rw [Wcoeff_height_zero_succ]
          rw [show PowerSeries.coeff (R := R) (n + 1)
              (PowerSeries.C (c 0) * PowerSeries.X * W 0 a b c) =
                c 0 * Wcoeff 0 a b c n by
            rw [mul_assoc]
            simp]
    calc
      geomDenom (c 0) * W 0 a b c =
          W 0 a b c - PowerSeries.C (c 0) * PowerSeries.X * W 0 a b c := by
        simp [geomDenom]
        ring
      _ = 1 := by
        nth_rewrite 1 [hseries]
        abel
  have hleft :
      PowerSeries.invOfUnit (geomDenom (c 0)) (1 : Rˣ) * geomDenom (c 0) = 1 := by
    exact PowerSeries.invOfUnit_mul (geomDenom (c 0)) (1 : Rˣ)
      (by simp [geomDenom])
  calc
    W 0 a b c = 1 * W 0 a b c := by simp
    _ = (PowerSeries.invOfUnit (geomDenom (c 0)) (1 : Rˣ) * geomDenom (c 0)) *
        W 0 a b c := by rw [hleft]
    _ = PowerSeries.invOfUnit (geomDenom (c 0)) (1 : Rˣ) *
        (geomDenom (c 0) * W 0 a b c) := by ring
    _ = PowerSeries.invOfUnit (geomDenom (c 0)) (1 : Rˣ) := by rw [hmul, mul_one]

def cfDenom {R : Type*} [CommRing R]
    (a b c : ℕ → R) (tail : PowerSeries R) : PowerSeries R :=
  1 - PowerSeries.C (c 0) * PowerSeries.X -
    PowerSeries.C (a 0 * b 0) * PowerSeries.X ^ 2 * tail

@[simp] theorem constantCoeff_cfDenom {R : Type*} [CommRing R]
    (a b c : ℕ → R) (tail : PowerSeries R) :
    PowerSeries.constantCoeff (cfDenom a b c tail) = 1 := by
  simp [cfDenom]

/-- The finite J-fraction tail, measured from the current bottom level. -/
def JFraction {R : Type*} [CommRing R] :
    ℕ → (ℕ → R) → (ℕ → R) → (ℕ → R) → PowerSeries R
  | 0, _a, _b, c =>
      PowerSeries.invOfUnit (geomDenom (c 0)) (1 : Rˣ)
  | h + 1, a, b, c =>
      PowerSeries.invOfUnit
        (cfDenom a b c (JFraction h (shift a) (shift b) (shift c))) (1 : Rˣ)

@[simp] theorem JFraction_zero {R : Type*} [CommRing R] (a b c : ℕ → R) :
    JFraction 0 a b c =
      PowerSeries.invOfUnit (geomDenom (c 0)) (1 : Rˣ) := rfl

@[simp] theorem JFraction_succ {R : Type*} [CommRing R]
    (h : ℕ) (a b c : ℕ → R) :
    JFraction (h + 1) a b c =
      PowerSeries.invOfUnit
        (cfDenom a b c (JFraction h (shift a) (shift b) (shift c))) (1 : Rˣ) := rfl

theorem coeff_quadratic_term {R : Type*} [CommRing R]
    (A : R) (P Q : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff (R := R) (n + 2)
        (PowerSeries.C A * PowerSeries.X ^ 2 * (P * Q)) =
      A * ∑ i : Fin (n + 1),
        PowerSeries.coeff (R := R) i.1 P *
          PowerSeries.coeff (R := R) (n - i.1) Q := by
  rw [mul_assoc]
  simp only [PowerSeries.coeff_C_mul]
  rw [PowerSeries.coeff_X_pow_mul (p := P * Q) (n := 2) (d := n)]
  rw [PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun x y => PowerSeries.coeff (R := R) x P *
      PowerSeries.coeff (R := R) y Q) n]
  rw [Finset.sum_fin_eq_sum_range]
  apply congrArg (fun z => A * z)
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  simp [hi']

theorem W_first_return_series {R : Type*} [CommRing R]
    (h : ℕ) (a b c : ℕ → R) :
    W (h + 1) a b c =
      1 + PowerSeries.C (c 0) * PowerSeries.X * W (h + 1) a b c +
        PowerSeries.C (a 0 * b 0) * PowerSeries.X ^ 2 *
          (W h (shift a) (shift b) (shift c) * W (h + 1) a b c) := by
  ext n
  cases n with
  | zero =>
      simp
  | succ n =>
      cases n with
      | zero =>
          simp only [map_add, PowerSeries.coeff_one, coeff_W]
          rw [Wcoeff_succ_one]
          rw [show PowerSeries.coeff (R := R) 1
              (PowerSeries.C (c 0) * PowerSeries.X * W (h + 1) a b c) = c 0 by
            rw [mul_assoc]
            simp]
          rw [show PowerSeries.coeff (R := R) 1
              (PowerSeries.C (a 0 * b 0) * PowerSeries.X ^ 2 *
                (W h (shift a) (shift b) (shift c) * W (h + 1) a b c)) = 0 by
            simp only [mul_assoc, PowerSeries.coeff_C_mul]
            rw [PowerSeries.coeff_X_pow_mul'
              (p := W h (shift a) (shift b) (shift c) * W (h + 1) a b c)
              (n := 2) (d := 1)]
            simp]
          simp
      | succ m =>
          simp only [map_add, PowerSeries.coeff_one, Nat.succ_ne_zero, ↓reduceIte,
            zero_add, coeff_W]
          rw [show m + 1 + 1 = m + 2 by omega]
          rw [Wcoeff_succ_succ]
          rw [show PowerSeries.coeff (R := R) (m + 2)
              (PowerSeries.C (c 0) * PowerSeries.X * W (h + 1) a b c) =
                c 0 * Wcoeff (h + 1) a b c (m + 1) by
            rw [mul_assoc]
            simp]
          rw [coeff_quadratic_term]
          simp [coeff_W]

theorem W_mul_cfDenom_self {R : Type*} [CommRing R]
    (h : ℕ) (a b c : ℕ → R) :
    cfDenom a b c (W h (shift a) (shift b) (shift c)) * W (h + 1) a b c = 1 := by
  have hfr := W_first_return_series h a b c
  calc
    cfDenom a b c (W h (shift a) (shift b) (shift c)) * W (h + 1) a b c =
        W (h + 1) a b c -
          PowerSeries.C (c 0) * PowerSeries.X * W (h + 1) a b c -
          PowerSeries.C (a 0 * b 0) * PowerSeries.X ^ 2 *
            (W h (shift a) (shift b) (shift c) * W (h + 1) a b c) := by
      simp [cfDenom]
      ring
    _ = 1 := by
      nth_rewrite 1 [hfr]
      abel

/-- Flajolet's finite continued-fraction theorem, bounded height. -/
theorem flajolet_cf {R : Type*} [CommRing R]
    (h : ℕ) (a b c : ℕ → R) :
    W h a b c = JFraction h a b c := by
  induction h generalizing a b c with
  | zero =>
      exact W_height_zero_eq_inv a b c
  | succ h ih =>
      have htail :
          W h (shift a) (shift b) (shift c) =
            JFraction h (shift a) (shift b) (shift c) := ih _ _ _
      have hmul :
          cfDenom a b c (JFraction h (shift a) (shift b) (shift c)) *
              W (h + 1) a b c = 1 := by
        simpa [htail] using W_mul_cfDenom_self h a b c
      have hleft :
          PowerSeries.invOfUnit
              (cfDenom a b c (JFraction h (shift a) (shift b) (shift c))) (1 : Rˣ) *
            cfDenom a b c (JFraction h (shift a) (shift b) (shift c)) = 1 := by
        exact PowerSeries.invOfUnit_mul
          (cfDenom a b c (JFraction h (shift a) (shift b) (shift c))) (1 : Rˣ)
          (by simp)
      calc
        W (h + 1) a b c = 1 * W (h + 1) a b c := by simp
        _ =
            (PowerSeries.invOfUnit
                (cfDenom a b c (JFraction h (shift a) (shift b) (shift c))) (1 : Rˣ) *
              cfDenom a b c (JFraction h (shift a) (shift b) (shift c))) *
                W (h + 1) a b c := by rw [hleft]
        _ =
            PowerSeries.invOfUnit
                (cfDenom a b c (JFraction h (shift a) (shift b) (shift c))) (1 : Rˣ) *
              (cfDenom a b c (JFraction h (shift a) (shift b) (shift c)) *
                W (h + 1) a b c) := by ring
        _ =
            PowerSeries.invOfUnit
                (cfDenom a b c (JFraction h (shift a) (shift b) (shift c))) (1 : Rˣ) := by
          rw [hmul, mul_one]
        _ = JFraction (h + 1) a b c := rfl

/-- The requested explicit height-one case. -/
theorem flajolet_cf_height_one {R : Type*} [CommRing R] (a b c : ℕ → R) :
    W 1 a b c = JFraction 1 a b c := by
  exact flajolet_cf 1 a b c

end

end AnalyticCombinatorics.Ch5.ContinuedFractions
