import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-! # Ch III — Inversion Polynomials and q-Analogs

This file formalizes inversion polynomials, q-analogs of permutation statistics,
and the Euler–Mahonian distribution from Flajolet & Sedgewick's
*Analytic Combinatorics*, Chapter III.

Central topics:
- **Permutation statistics**: inversions, descents, major index on lists
- **q-analogs**: q-bracket `[n]_q`, q-factorial `[n]_q!`, Gaussian binomial `[n,k]_q`
- **Inversion polynomial**: `∑_{σ ∈ S_n} q^{inv(σ)} = [n]_q!`
- **MacMahon equidistribution**: `inv` and `maj` are equidistributed over `S_n`
- **Carlitz q-Eulerian numbers**: `A_{n,k}(q)` and the Euler–Mahonian distribution
-/

namespace InversionPolynomials

-- ============================================================
-- Section 1: Permutation statistics on lists
-- ============================================================

/-!
## Permutation Statistics

A permutation of `[n]` is represented as a list `[σ(0), σ(1), …, σ(n-1)]`
containing `{0, 1, …, n-1}` in some order.

- **Inversion**: a pair `(i,j)` with `i < j` and `σ(i) > σ(j)`
- **Descent**: a position `i` where `σ(i) > σ(i+1)`
- **Major index**: `maj(σ) = ∑ {i+1 : σ(i) > σ(i+1)}` (sum of 1-indexed descent positions)
-/

/-- Count elements strictly less than `a` in a list. -/
def countLess (a : ℕ) : List ℕ → ℕ
  | [] => 0
  | b :: rest => (if b < a then 1 else 0) + countLess a rest

/-- Number of inversions in a permutation represented as a list. -/
def invCount : List ℕ → ℕ
  | [] => 0
  | a :: rest => countLess a rest + invCount rest

/-- Number of descents: positions `i` where `l[i] > l[i+1]`. -/
def descentCount : List ℕ → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: rest => (if a > b then 1 else 0) + descentCount (b :: rest)

/-- Auxiliary for major index: tracks current 1-indexed position. -/
def majorIndexAux : List ℕ → ℕ → ℕ
  | [], _ => 0
  | [_], _ => 0
  | a :: b :: rest, pos =>
    (if a > b then pos else 0) + majorIndexAux (b :: rest) (pos + 1)

/-- Major index: sum of 1-indexed descent positions. -/
def majorIndex (l : List ℕ) : ℕ := majorIndexAux l 1

/-! ### Spot checks on permutations of [3] -/

example : invCount [0, 1, 2] = 0 := by native_decide
example : invCount [0, 2, 1] = 1 := by native_decide
example : invCount [1, 0, 2] = 1 := by native_decide
example : invCount [1, 2, 0] = 2 := by native_decide
example : invCount [2, 0, 1] = 2 := by native_decide
example : invCount [2, 1, 0] = 3 := by native_decide

example : descentCount [0, 1, 2] = 0 := by native_decide
example : descentCount [2, 0, 1] = 1 := by native_decide
example : descentCount [2, 1, 0] = 2 := by native_decide

example : majorIndex [0, 1, 2] = 0 := by native_decide
example : majorIndex [0, 2, 1] = 2 := by native_decide
example : majorIndex [1, 0, 2] = 1 := by native_decide
example : majorIndex [1, 2, 0] = 2 := by native_decide
example : majorIndex [2, 0, 1] = 1 := by native_decide
example : majorIndex [2, 1, 0] = 3 := by native_decide

/-! ### Reverse permutation: max inversions = C(n,2), max major index = C(n,2) -/

example : invCount [3, 2, 1, 0] = 6 := by native_decide
example : descentCount [3, 2, 1, 0] = 3 := by native_decide
example : majorIndex [3, 2, 1, 0] = 6 := by native_decide

-- ============================================================
-- Section 2: q-Bracket and q-Factorial
-- ============================================================

/-!
## q-Bracket and q-Factorial

The **q-bracket** `[n]_q = 1 + q + q² + ⋯ + q^{n-1}` is the q-analog of `n`.

The **q-factorial** `[n]_q! = [1]_q · [2]_q · ⋯ · [n]_q` is the q-analog of `n!`.

At `q = 1`: `[n]_1 = n` and `[n]_1! = n!`.
-/

/-- q-bracket `[n]_q = 1 + q + q² + ⋯ + q^{n-1}`. -/
def qBracket (q n : ℕ) : ℕ := ∑ i ∈ Finset.range n, q ^ i

example : qBracket 1 5 = 5 := by native_decide
example : qBracket 2 1 = 1 := by native_decide
example : qBracket 2 2 = 3 := by native_decide
example : qBracket 2 3 = 7 := by native_decide
example : qBracket 2 4 = 15 := by native_decide
example : qBracket 3 3 = 13 := by native_decide

/-- q-factorial `[n]_q! = [1]_q · [2]_q · ⋯ · [n]_q`. -/
def qFactorial (q : ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => qFactorial q n * qBracket q (n + 1)

example : qFactorial 1 0 = 1 := by native_decide
example : qFactorial 1 3 = 6 := by native_decide
example : qFactorial 1 4 = 24 := by native_decide
example : qFactorial 1 5 = 120 := by native_decide

example : qFactorial 2 2 = 3 := by native_decide
example : qFactorial 2 3 = 21 := by native_decide
example : qFactorial 2 4 = 315 := by native_decide

-- ============================================================
-- Section 3: Gaussian Binomial Coefficient
-- ============================================================

/-!
## Gaussian Binomial Coefficient (q-Binomial)

The **Gaussian binomial** `[n choose k]_q` is the q-analog of the
ordinary binomial coefficient, defined by the recurrence:

  `[n+1, k+1]_q = [n, k]_q + q^{k+1} · [n, k+1]_q`

At `q = 1`, it reduces to `C(n, k)`.
-/

/-- Gaussian binomial `[n, k]_q` via standard recurrence. -/
def qBinom (q : ℕ) : ℕ → ℕ → ℕ
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => qBinom q n k + q ^ (k + 1) * qBinom q n (k + 1)
termination_by n _ => n

/-! ### At q = 1: recovers ordinary binomial -/

example : qBinom 1 4 0 = Nat.choose 4 0 := by native_decide
example : qBinom 1 4 1 = Nat.choose 4 1 := by native_decide
example : qBinom 1 4 2 = Nat.choose 4 2 := by native_decide
example : qBinom 1 5 2 = Nat.choose 5 2 := by native_decide
example : qBinom 1 5 3 = Nat.choose 5 3 := by native_decide
example : qBinom 1 6 3 = Nat.choose 6 3 := by native_decide

/-! ### At q = 2 -/

example : qBinom 2 3 1 = 7 := by native_decide
example : qBinom 2 3 2 = 7 := by native_decide
example : qBinom 2 4 1 = 15 := by native_decide
example : qBinom 2 4 2 = 35 := by native_decide
example : qBinom 2 4 3 = 15 := by native_decide

/-! ### Symmetry: [n, k]_q = [n, n-k]_q -/

theorem qBinom_symm_3 :
    qBinom 2 3 1 = qBinom 2 3 2 := by native_decide
theorem qBinom_symm_4_1 :
    qBinom 2 4 1 = qBinom 2 4 3 := by native_decide
theorem qBinom_symm_5_2 :
    qBinom 2 5 2 = qBinom 2 5 3 := by native_decide

-- ============================================================
-- Section 4: Inversion Number Distribution
-- ============================================================

/-!
## Inversion Number Distribution

`inversionNumber n k` counts permutations of `[n]` with exactly `k` inversions.
The generating polynomial is the **inversion polynomial** `I_n(q) = [n]_q!`.

The distribution is symmetric: `I(n, k) = I(n, C(n,2) - k)`.
-/

/-- Number of permutations of `[n]` with exactly `k` inversions. -/
def inversionNumber : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k =>
    ∑ j ∈ Finset.range (min (k + 1) (n + 1)), inversionNumber n (k - j)
termination_by n k => (n, k)

-- I(3, k) = [1, 2, 2, 1]
example : inversionNumber 3 0 = 1 := by native_decide
example : inversionNumber 3 1 = 2 := by native_decide
example : inversionNumber 3 2 = 2 := by native_decide
example : inversionNumber 3 3 = 1 := by native_decide

-- I(4, k) = [1, 3, 5, 6, 5, 3, 1]
example : inversionNumber 4 0 = 1 := by native_decide
example : inversionNumber 4 1 = 3 := by native_decide
example : inversionNumber 4 2 = 5 := by native_decide
example : inversionNumber 4 3 = 6 := by native_decide
example : inversionNumber 4 4 = 5 := by native_decide
example : inversionNumber 4 5 = 3 := by native_decide
example : inversionNumber 4 6 = 1 := by native_decide

-- Row sums = n!
theorem invNum_rowSum_3 :
    ∑ k ∈ Finset.range 4, inversionNumber 3 k = 6 := by native_decide
theorem invNum_rowSum_4 :
    ∑ k ∈ Finset.range 7, inversionNumber 4 k = 24 := by native_decide

-- Symmetry
theorem invNum_symm_3 :
    ∀ k : Fin 4,
      inversionNumber 3 k.val = inversionNumber 3 (3 - k.val) := by
  native_decide
theorem invNum_symm_4 :
    ∀ k : Fin 7,
      inversionNumber 4 k.val = inversionNumber 4 (6 - k.val) := by
  native_decide

-- ============================================================
-- Section 5: Inversion Polynomial = q-Factorial
-- ============================================================

/-!
## Inversion Polynomial Identity

The fundamental identity of inversion polynomials states:

  `∑_{σ ∈ S_n} q^{inv(σ)} = [n]_q!`

This connects the combinatorial statistic (inversions) to the algebraic q-factorial.
We verify computationally using the recurrence-based inversion number distribution:
`I_n(q) = ∑_k I(n,k) · q^k = [n]_q!`.
-/

/-- Evaluate the inversion polynomial via the distribution: `∑_k I(n,k) · q^k`. -/
def invPolyEval (q n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n * (n - 1) / 2 + 1),
    inversionNumber n k * q ^ k

theorem invPoly_eq_qFact_2_1 :
    invPolyEval 2 1 = qFactorial 2 1 := by native_decide
theorem invPoly_eq_qFact_2_2 :
    invPolyEval 2 2 = qFactorial 2 2 := by native_decide
theorem invPoly_eq_qFact_2_3 :
    invPolyEval 2 3 = qFactorial 2 3 := by native_decide
theorem invPoly_eq_qFact_2_4 :
    invPolyEval 2 4 = qFactorial 2 4 := by native_decide
theorem invPoly_eq_qFact_3_3 :
    invPolyEval 3 3 = qFactorial 3 3 := by native_decide
theorem invPoly_eq_qFact_3_4 :
    invPolyEval 3 4 = qFactorial 3 4 := by native_decide

-- ============================================================
-- Section 6: MacMahon Equidistribution
-- ============================================================

/-!
## MacMahon Equidistribution

MacMahon's theorem (1913) states that inversions and major index have the
same distribution over S_n: for every `n` and `k`,

  `|{σ ∈ S_n : inv(σ) = k}| = |{σ ∈ S_n : maj(σ) = k}|`

Equivalently: `∑_{σ} q^{inv(σ)} = ∑_{σ} q^{maj(σ)} = [n]_q!`.
-/

/-- Count permutations of `[n]` with inversion number `k` (via list enumeration). -/
def invDistrib (n k : ℕ) : ℕ :=
  ((List.range n).permutations.filter fun σ => invCount σ = k).length

/-- Count permutations of `[n]` with major index `k` (via list enumeration). -/
def majDistrib (n k : ℕ) : ℕ :=
  ((List.range n).permutations.filter fun σ =>
    majorIndex σ = k).length

-- Both distributions for n = 3 are [1, 2, 2, 1]
theorem invDistrib_3 :
    invDistrib 3 0 = 1 ∧ invDistrib 3 1 = 2 ∧
    invDistrib 3 2 = 2 ∧ invDistrib 3 3 = 1 := by native_decide

theorem majDistrib_3 :
    majDistrib 3 0 = 1 ∧ majDistrib 3 1 = 2 ∧
    majDistrib 3 2 = 2 ∧ majDistrib 3 3 = 1 := by native_decide

-- MacMahon equidistribution verified for n = 3
theorem macmahon_check_3 :
    ∀ k : Fin 4,
      invDistrib 3 k.val = majDistrib 3 k.val := by native_decide

-- MacMahon equidistribution verified for n = 4
theorem macmahon_check_4 :
    ∀ k : Fin 7,
      invDistrib 4 k.val = majDistrib 4 k.val := by native_decide

-- Consistency: list-based invDistrib matches recurrence-based inversionNumber
theorem invDistrib_eq_invNum_3 :
    ∀ k : Fin 4,
      invDistrib 3 k.val = inversionNumber 3 k.val := by native_decide

-- ============================================================
-- Section 7: Carlitz q-Eulerian Numbers
-- ============================================================

/-!
## Carlitz q-Eulerian Numbers and the Euler–Mahonian Distribution

The **Carlitz q-Eulerian number** `A_{n,k}(q)` refines the Eulerian number
by incorporating the major index. It satisfies:

  `A_{n+1,k+1}(q) = [k+2]_q · A_{n,k+1}(q) + q^{k+1} · [n-k]_q · A_{n,k}(q)`

At `q = 1`, this reduces to the standard Eulerian recurrence.

The **Euler–Mahonian identity** states:

  `∑_{σ : des(σ) = k} q^{maj(σ)} = A_{n,k}(q)`
-/

/-- Carlitz q-Eulerian number `A_{n,k}(q)` evaluated at natural number `q`. -/
def qEulerianNum (q : ℕ) : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 =>
    if k + 1 < n + 1 then
      qBracket q (k + 2) * qEulerianNum q n (k + 1) +
      q ^ (k + 1) * qBracket q (n - k) * qEulerianNum q n k
    else 0
termination_by n _ => n

/-! ### At q = 1: ordinary Eulerian numbers -/

-- A(3, k) = [1, 4, 1]
example : qEulerianNum 1 3 0 = 1 := by native_decide
example : qEulerianNum 1 3 1 = 4 := by native_decide
example : qEulerianNum 1 3 2 = 1 := by native_decide

-- A(4, k) = [1, 11, 11, 1]
example : qEulerianNum 1 4 0 = 1 := by native_decide
example : qEulerianNum 1 4 1 = 11 := by native_decide
example : qEulerianNum 1 4 2 = 11 := by native_decide
example : qEulerianNum 1 4 3 = 1 := by native_decide

/-! ### At q = 2 -/

example : qEulerianNum 2 3 0 = 1 := by native_decide
example : qEulerianNum 2 3 1 = 12 := by native_decide
example : qEulerianNum 2 3 2 = 8 := by native_decide

-- Sum of q-Eulerian numbers = q-factorial
theorem qEulerian_sum_3 :
    qEulerianNum 2 3 0 + qEulerianNum 2 3 1 +
    qEulerianNum 2 3 2 = qFactorial 2 3 := by native_decide

theorem qEulerian_sum_4 :
    qEulerianNum 2 4 0 + qEulerianNum 2 4 1 +
    qEulerianNum 2 4 2 + qEulerianNum 2 4 3 =
    qFactorial 2 4 := by native_decide

/-! ### Euler–Mahonian distribution: direct enumeration -/

/-- Evaluate the Euler–Mahonian polynomial for descent number `d`:
`∑_{σ : des(σ)=d} q^{maj(σ)}` at a given `q`. Uses list enumeration. -/
def eulerMahonianEval (q n d : ℕ) : ℕ :=
  (List.range n).permutations.foldl
    (fun acc σ => acc + if descentCount σ = d then q ^ majorIndex σ else 0) 0

-- Verify Carlitz identity for n = 3, q = 2
theorem eulerMahonian_2_3_0 :
    eulerMahonianEval 2 3 0 = qEulerianNum 2 3 0 := by native_decide
theorem eulerMahonian_2_3_1 :
    eulerMahonianEval 2 3 1 = qEulerianNum 2 3 1 := by native_decide
theorem eulerMahonian_2_3_2 :
    eulerMahonianEval 2 3 2 = qEulerianNum 2 3 2 := by native_decide

-- Verify Carlitz identity for n = 4, q = 2
theorem eulerMahonian_2_4_0 :
    eulerMahonianEval 2 4 0 = qEulerianNum 2 4 0 := by native_decide
theorem eulerMahonian_2_4_1 :
    eulerMahonianEval 2 4 1 = qEulerianNum 2 4 1 := by native_decide
theorem eulerMahonian_2_4_2 :
    eulerMahonianEval 2 4 2 = qEulerianNum 2 4 2 := by native_decide
theorem eulerMahonian_2_4_3 :
    eulerMahonianEval 2 4 3 = qEulerianNum 2 4 3 := by native_decide

-- ============================================================
-- Section 8: General Theorems (proof deferred)
-- ============================================================

/-!
## General Theorems

The following theorems state fundamental identities in full generality.
Their proofs are deferred (`sorry`).
-/

/-- **MacMahon's equidistribution**: `inv` and `maj` have the same
distribution over `S_n`. -/
theorem macmahon_equidistribution (n k : ℕ) :
    invDistrib n k = majDistrib n k := by
  sorry

/-- **Inversion polynomial identity**: `∑_k I(n,k) · q^k = [n]_q!`. -/
theorem invPoly_eq_qFactorial (q n : ℕ) :
    invPolyEval q n = qFactorial q n := by
  sorry

/-- At `q = 1`, the q-bracket gives `n`. -/
theorem qBracket_at_one (n : ℕ) : qBracket 1 n = n := by
  sorry

/-- At `q = 1`, the q-factorial gives `n!`. -/
theorem qFactorial_at_one (n : ℕ) :
    qFactorial 1 n = n.factorial := by
  sorry

/-- At `q = 1`, the Gaussian binomial gives the ordinary binomial. -/
theorem qBinom_at_one (n k : ℕ) :
    qBinom 1 n k = Nat.choose n k := by
  sorry

/-- The Gaussian binomial is symmetric: `[n, k]_q = [n, n-k]_q`. -/
theorem qBinom_symmetry (q n k : ℕ) (hk : k ≤ n) :
    qBinom q n k = qBinom q n (n - k) := by
  sorry

/-- **Carlitz's Euler–Mahonian identity**:
`∑_{σ : des(σ)=k} q^{maj(σ)} = A_{n,k}(q)`. -/
theorem carlitz_euler_mahonian (q n k : ℕ) :
    eulerMahonianEval q n k = qEulerianNum q n k := by
  sorry

/-- The q-factorial decomposes as `[n]_q! = ∑_k A_{n,k}(q)`. -/
theorem qFactorial_eq_sum_qEulerian (q n : ℕ) :
    qFactorial q n =
      ∑ k ∈ Finset.range n, qEulerianNum q n k := by
  sorry

/-- Row sum of the inversion number distribution equals `n!`. -/
theorem inversionNumber_rowSum (n : ℕ) :
    ∑ k ∈ Finset.range (n * (n - 1) / 2 + 1),
      inversionNumber n k = n.factorial := by
  sorry

/-- The inversion number distribution is symmetric. -/
theorem inversionNumber_symmetry (n k : ℕ)
    (hk : k ≤ n * (n - 1) / 2) :
    inversionNumber n k =
      inversionNumber n (n * (n - 1) / 2 - k) := by
  sorry

/-! ### Verified finite instances of the general theorems -/

theorem qBracket_at_one_check (n : ℕ) (hn : n ≤ 10) :
    qBracket 1 n = n := by
  interval_cases n <;> native_decide

theorem qFactorial_at_one_check (n : ℕ) (hn : n ≤ 7) :
    qFactorial 1 n = n.factorial := by
  interval_cases n <;> native_decide

theorem qBinom_at_one_check (n : ℕ) (hn : n ≤ 5)
    (k : ℕ) (hk : k ≤ n) :
    qBinom 1 n k = Nat.choose n k := by
  interval_cases n <;> interval_cases k <;> native_decide

theorem inversionNumber_rowSum_check (n : ℕ) (hn : n ≤ 5) :
    ∑ k ∈ Finset.range (n * (n - 1) / 2 + 1),
      inversionNumber n k = n.factorial := by
  interval_cases n <;> native_decide

end InversionPolynomials
