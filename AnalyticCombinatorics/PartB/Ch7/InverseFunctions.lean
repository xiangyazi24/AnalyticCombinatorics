import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace InverseFunctions

/-!
  Chapter VII inverse-function schemas, recorded as executable coefficient
  checks.  We work only with finite numerical statements that Lean can decide.
-/

-- ============================================================
-- §1  Lagrange inversion: T = z * phi(T)
-- ============================================================

/-- Coefficient of `z^k` in the `p`th power of a formal series with coefficients `a`. -/
def coeffPower (a : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, k => if k = 0 then 1 else 0
  | p + 1, k => ∑ i ∈ Finset.range (k + 1), a i * coeffPower a p (k - i)

/-- Lagrange coefficient formula for `T = z * phi(T)`, for `n ≥ 1`. -/
def lagrangeCoeff (phi : ℕ → ℕ) (n : ℕ) : ℕ :=
  if n = 0 then 0 else coeffPower phi n (n - 1) / n

-- ============================================================
-- §2  Binary trees: T = z(1+T)^2
-- ============================================================

/-- Coefficients of `phi(u) = (1 + u)^2 = 1 + 2u + u^2`. -/
def binaryPhi : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 1
  | _ => 0

/-- Coefficient of `z^n` in `T(z)` where `T = z(1+T)^2`. -/
def binaryTreeCoeff (n : ℕ) : ℕ := lagrangeCoeff binaryPhi n

/-- Catalan closed form for `[z^n]T(z)` in `T = z(1+T)^2`. -/
def catalan (n : ℕ) : ℕ := Nat.choose (2 * n) n / (n + 1)

theorem binaryTreeCoeff_values :
    [binaryTreeCoeff 1, binaryTreeCoeff 2, binaryTreeCoeff 3,
     binaryTreeCoeff 4, binaryTreeCoeff 5, binaryTreeCoeff 6] =
    [1, 2, 5, 14, 42, 132] := by
  native_decide

theorem binaryTreeCoeff_eq_catalan_1_8 :
    ∀ n : Fin 8, binaryTreeCoeff (n.val + 1) = catalan (n.val + 1) := by
  native_decide

theorem binaryTreeCoeff_lagrange_1_8 :
    ∀ n : Fin 8,
      binaryTreeCoeff (n.val + 1) =
        Nat.choose (2 * (n.val + 1)) n.val / (n.val + 1) := by
  native_decide

/-- `[z^n]T = (1/n)[z^(n-1)]phi(z)^n`, checked for `phi(u) = (1+u)^2`. -/
theorem binaryTreeCoeff_lagrange_rule_1_8 :
    ∀ n : Fin 8,
      binaryTreeCoeff (n.val + 1) =
        coeffPower binaryPhi (n.val + 1) n.val / (n.val + 1) := by
  native_decide

-- ============================================================
-- §3  Cayley tree function: T = z * exp(T)
-- ============================================================

/-- Coefficient of `z^n` in the Cayley tree EGF `T = z exp(T)`. -/
def cayleyEGFCoeff (n : ℕ) : ℚ :=
  if n = 0 then 0 else (n ^ (n - 1) : ℚ) / (Nat.factorial n : ℚ)

/-- The integer numerator `n! [z^n]T(z) = n^(n-1)` for labelled rooted trees. -/
def cayleyLabelledCount (n : ℕ) : ℕ := if n = 0 then 0 else n ^ (n - 1)

theorem cayleyLabelledCount_values :
    [cayleyLabelledCount 1, cayleyLabelledCount 2, cayleyLabelledCount 3,
     cayleyLabelledCount 4, cayleyLabelledCount 5, cayleyLabelledCount 6] =
    [1, 2, 9, 64, 625, 7776] := by
  native_decide

theorem cayleyEGFCoeff_scaled_1_7 :
    ∀ n : Fin 7,
      (Nat.factorial (n.val + 1) : ℚ) * cayleyEGFCoeff (n.val + 1) =
        ((n.val + 1) ^ n.val : ℕ) := by
  native_decide

theorem cayleyFormula_small :
    ∀ n : Fin 7, cayleyLabelledCount (n.val + 1) = (n.val + 1) ^ n.val := by
  native_decide

-- ============================================================
-- §4  Motzkin numbers: M = 1 + zM + z^2 M^2
-- ============================================================

/-- Motzkin numbers from the closed-form coefficient sum. -/
def motzkin (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n / 2 + 1),
    Nat.choose n (2 * k) * Nat.choose (2 * k) k / (k + 1)

/-- First Motzkin coefficients for `M = 1 + zM + z^2 M^2`. -/
def motzkinTable : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 4
  | 4 => 9
  | 5 => 21
  | 6 => 51
  | 7 => 127
  | 8 => 323
  | 9 => 835
  | 10 => 2188
  | _ => 0

theorem motzkinTable_values :
    [motzkinTable 0, motzkinTable 1, motzkinTable 2, motzkinTable 3,
     motzkinTable 4, motzkinTable 5, motzkinTable 6, motzkinTable 7,
     motzkinTable 8, motzkinTable 9, motzkinTable 10] =
    [1, 1, 2, 4, 9, 21, 51, 127, 323, 835, 2188] := by
  native_decide

theorem motzkinTable_matches_formula :
    ∀ n : Fin 11, motzkinTable n.val = motzkin n.val := by
  native_decide

/-- Coefficient recurrence induced by `M = 1 + zM + z^2 M^2`. -/
theorem motzkin_implicit_recurrence_2_10 :
    ∀ n : Fin 9,
      motzkinTable (n.val + 2) =
        motzkinTable (n.val + 1) +
          ∑ k ∈ Finset.range (n.val + 1),
            motzkinTable k * motzkinTable (n.val - k) := by
  native_decide

-- ============================================================
-- §5  Ternary trees: T = 1 + zT^3
-- ============================================================

/-- Ternary tree numbers `[z^n]T(z)` for `T = 1 + zT^3`. -/
def ternaryTreeCoeff (n : ℕ) : ℕ :=
  Nat.choose (3 * n) n / (2 * n + 1)

def ternaryTreeTable : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 3
  | 3 => 12
  | 4 => 55
  | 5 => 273
  | 6 => 1428
  | 7 => 7752
  | _ => 0

theorem ternaryTreeTable_values :
    [ternaryTreeTable 0, ternaryTreeTable 1, ternaryTreeTable 2,
     ternaryTreeTable 3, ternaryTreeTable 4, ternaryTreeTable 5,
     ternaryTreeTable 6, ternaryTreeTable 7] =
    [1, 1, 3, 12, 55, 273, 1428, 7752] := by
  native_decide

theorem ternaryTreeTable_matches_formula :
    ∀ n : Fin 8, ternaryTreeTable n.val = ternaryTreeCoeff n.val := by
  native_decide

/-- Coefficient recurrence induced by `T = 1 + zT^3`. -/
theorem ternaryTree_implicit_recurrence_1_7 :
    ∀ n : Fin 7,
      ternaryTreeTable (n.val + 1) =
        ∑ i ∈ Finset.range (n.val + 1),
          ∑ j ∈ Finset.range (n.val - i + 1),
            ternaryTreeTable i * ternaryTreeTable j *
              ternaryTreeTable (n.val - i - j) := by
  native_decide

-- ============================================================
-- §6  General m-ary tree counts: Fuss-Catalan
-- ============================================================

/-- General `m`-ary tree count with `n` internal nodes:
    `binom(mn,n)/(mn-n+1)`. -/
def fussCatalan (m n : ℕ) : ℕ :=
  Nat.choose (m * n) n / (m * n - n + 1)

theorem fussCatalan_binary_matches :
    ∀ n : Fin 8, fussCatalan 2 n.val = catalan n.val := by
  native_decide

theorem fussCatalan_ternary_matches :
    ∀ n : Fin 8, fussCatalan 3 n.val = ternaryTreeCoeff n.val := by
  native_decide

theorem fussCatalan_quaternary_values :
    [fussCatalan 4 0, fussCatalan 4 1, fussCatalan 4 2,
     fussCatalan 4 3, fussCatalan 4 4, fussCatalan 4 5] =
    [1, 1, 4, 22, 140, 969] := by
  native_decide

theorem fussCatalan_formula_small :
    ∀ m : Fin 5, ∀ n : Fin 6,
      fussCatalan (m.val + 1) n.val =
        Nat.choose ((m.val + 1) * n.val) n.val /
          ((m.val + 1) * n.val - n.val + 1) := by
  native_decide

end InverseFunctions
