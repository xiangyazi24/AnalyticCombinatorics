import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace MotzkinPaths

/-!
  Chapter I examples around Motzkin paths.

  The file keeps the finite numerical claims computational: Motzkin numbers,
  ordinary and centered trinomial coefficients, the Catalan expansion, and a
  small Riordan-array table are all verified by `native_decide`.
-/

/-! ## Motzkin paths as restricted Dyck paths -/

/-- The three allowed steps of a Motzkin path. -/
inductive MotzkinStep where
  | up
  | flat
  | down
deriving DecidableEq, Repr

open MotzkinStep

/-- All words of length `n` over the three Motzkin steps. -/
def allStepLists : ℕ → List (List MotzkinStep)
  | 0 => [[]]
  | n + 1 =>
      (allStepLists n).flatMap fun p => [up :: p, flat :: p, down :: p]

/-- A Motzkin path starts at height `0`, never goes negative, and ends at `0`. -/
def validFromHeight : ℕ → List MotzkinStep → Bool
  | h, [] => h == 0
  | h, up :: p => validFromHeight (h + 1) p
  | h, flat :: p => validFromHeight h p
  | 0, down :: _ => false
  | h + 1, down :: p => validFromHeight h p

/-- A restricted Dyck/Motzkin path is a Dyck-like path with up, down, and flat steps. -/
def IsRestrictedDyckMotzkinPath (p : List MotzkinStep) : Bool :=
  validFromHeight 0 p

/-- Counts restricted Dyck paths with up/down/flat steps. -/
def restrictedDyckMotzkinCount (n : ℕ) : ℕ :=
  ((allStepLists n).filter IsRestrictedDyckMotzkinPath).length

/-! ## Motzkin numbers -/

/-- First Motzkin numbers, tabulated as requested. -/
def motzkinTable : Fin 8 → ℕ := ![1, 1, 2, 4, 9, 21, 51, 127]

/-- The tabulated Motzkin number, with `0` outside the verified table. -/
def motzkinNumber : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 4
  | 4 => 9
  | 5 => 21
  | 6 => 51
  | 7 => 127
  | _ => 0

theorem motzkin_zero : motzkinNumber 0 = 1 := by native_decide
theorem motzkin_one : motzkinNumber 1 = 1 := by native_decide
theorem motzkin_two : motzkinNumber 2 = 2 := by native_decide
theorem motzkin_three : motzkinNumber 3 = 4 := by native_decide
theorem motzkin_four : motzkinNumber 4 = 9 := by native_decide
theorem motzkin_five : motzkinNumber 5 = 21 := by native_decide
theorem motzkin_six : motzkinNumber 6 = 51 := by native_decide
theorem motzkin_seven : motzkinNumber 7 = 127 := by native_decide

theorem motzkin_table_matches_number :
    (fun i : Fin 8 => motzkinNumber i.val) = motzkinTable := by
  native_decide

/-- The Motzkin recurrence, checked on the finite table through `M(7)`. -/
theorem motzkin_recurrence_checked :
    ∀ n : Fin 7,
      motzkinNumber (n.val + 1) =
        motzkinNumber n.val +
          ∑ k ∈ Finset.range n.val,
            motzkinNumber k * motzkinNumber (n.val - 1 - k) := by
  native_decide

theorem restricted_dyck_counts_match_motzkin_table :
    (fun i : Fin 8 => restrictedDyckMotzkinCount i.val) = motzkinTable := by
  native_decide

theorem restricted_dyck_count_seven :
    restrictedDyckMotzkinCount 7 = 127 := by
  native_decide

/-! ## Trinomial coefficients -/

/-- Coefficient of `x^k` in `(1 + x + x^2)^n`. -/
def trinomialCoeff : ℕ → ℕ → ℕ
  | 0, k => if k = 0 then 1 else 0
  | n + 1, k =>
      trinomialCoeff n k +
        (if k = 0 then 0 else trinomialCoeff n (k - 1)) +
        (if k < 2 then 0 else trinomialCoeff n (k - 2))

theorem trinomial_row_three_prefix :
    (fun k : Fin 4 => trinomialCoeff 3 k.val) = ![1, 3, 6, 7] := by
  native_decide

theorem trinomial_three_zero : trinomialCoeff 3 0 = 1 := by native_decide
theorem trinomial_three_one : trinomialCoeff 3 1 = 3 := by native_decide
theorem trinomial_three_two : trinomialCoeff 3 2 = 6 := by native_decide
theorem trinomial_three_three : trinomialCoeff 3 3 = 7 := by native_decide

/--
  Centered trinomial coefficient: coefficient of `x^(n+k)` in
  `(1 + x + x^2)^n`, equivalently coefficient of `x^k` in `(x^-1 + 1 + x)^n`
  for nonnegative offset `k`.
-/
def centeredTrinomialCoeff (n k : ℕ) : ℕ :=
  trinomialCoeff n (n + k)

/-- Central trinomial coefficient: coefficient of `x^n` in `(1 + x + x^2)^n`. -/
def centralTrinomial (n : ℕ) : ℕ :=
  centeredTrinomialCoeff n 0

def centralTrinomialTable : Fin 7 → ℕ := ![1, 1, 3, 7, 19, 51, 141]

theorem central_trinomial_table_checked :
    (fun n : Fin 7 => centralTrinomial n.val) = centralTrinomialTable := by
  native_decide

theorem central_trinomial_zero : centralTrinomial 0 = 1 := by native_decide
theorem central_trinomial_one : centralTrinomial 1 = 1 := by native_decide
theorem central_trinomial_two : centralTrinomial 2 = 3 := by native_decide
theorem central_trinomial_three : centralTrinomial 3 = 7 := by native_decide
theorem central_trinomial_four : centralTrinomial 4 = 19 := by native_decide
theorem central_trinomial_five : centralTrinomial 5 = 51 := by native_decide
theorem central_trinomial_six : centralTrinomial 6 = 141 := by native_decide

/-! ## Motzkin-Catalan relation -/

/-- Catalan number `C_n = binom(2n,n)/(n+1)`. -/
def catalanNumber (n : ℕ) : ℕ :=
  Nat.choose (2 * n) n / (n + 1)

/-- Insert `n - 2k` flat steps into a Dyck path of semilength `k`. -/
def motzkinCatalanSum (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n / 2 + 1), Nat.choose n (2 * k) * catalanNumber k

theorem catalan_first_six :
    (fun k : Fin 6 => catalanNumber k.val) = ![1, 1, 2, 5, 14, 42] := by
  native_decide

theorem motzkin_catalan_relation_checked :
    ∀ n : Fin 6, motzkinNumber n.val = motzkinCatalanSum n.val := by
  native_decide

theorem motzkin_catalan_zero : motzkinCatalanSum 0 = 1 := by native_decide
theorem motzkin_catalan_one : motzkinCatalanSum 1 = 1 := by native_decide
theorem motzkin_catalan_two : motzkinCatalanSum 2 = 2 := by native_decide
theorem motzkin_catalan_three : motzkinCatalanSum 3 = 4 := by native_decide
theorem motzkin_catalan_four : motzkinCatalanSum 4 = 9 := by native_decide
theorem motzkin_catalan_five : motzkinCatalanSum 5 = 21 := by native_decide

/-! ## Riordan-array connection -/

/-- Convolution power of an ordinary generating function's coefficient sequence. -/
def coeffPower (a : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, n => if n = 0 then 1 else 0
  | m + 1, n => ∑ i ∈ Finset.range (n + 1), a i * coeffPower a m (n - i)

/--
  The ordinary Riordan array `(M(x), x M(x))` associated with Motzkin numbers:
  entry `(n,k)` is `[x^n] M(x) (x M(x))^k`.
-/
def motzkinRiordanEntry (n k : ℕ) : ℕ :=
  if k ≤ n then coeffPower motzkinNumber (k + 1) (n - k) else 0

theorem motzkin_riordan_first_column :
    ∀ n : Fin 8, motzkinRiordanEntry n.val 0 = motzkinNumber n.val := by
  native_decide

theorem motzkin_riordan_row_zero :
    (fun k : Fin 1 => motzkinRiordanEntry 0 k.val) = ![1] := by
  native_decide

theorem motzkin_riordan_row_three :
    (fun k : Fin 4 => motzkinRiordanEntry 3 k.val) = ![4, 5, 3, 1] := by
  native_decide

theorem motzkin_riordan_row_four :
    (fun k : Fin 5 => motzkinRiordanEntry 4 k.val) = ![9, 12, 9, 4, 1] := by
  native_decide

theorem motzkin_riordan_entry_three_one :
    motzkinRiordanEntry 3 1 = 5 := by
  native_decide

theorem motzkin_riordan_entry_four_two :
    motzkinRiordanEntry 4 2 = 9 := by
  native_decide

theorem motzkin_riordan_entry_five_three :
    motzkinRiordanEntry 5 3 = 14 := by
  native_decide

end MotzkinPaths
