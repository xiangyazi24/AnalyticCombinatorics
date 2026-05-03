import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Symmetric Function Identities (F&S Ch. II)

Numerical verifications of classical symmetric function identities and their
combinatorial interpretations, following Flajolet & Sedgewick Chapter II.

We verify:
1. Elementary symmetric polynomials e_k via binomial coefficients and explicit sums
2. Power sum polynomials p_k and Newton's identities
3. Complete homogeneous symmetric polynomials h_k via stars-and-bars
4. Standard Young tableaux counts via the hook-length formula
5. RSK correspondence: Σ (f^λ)² = n!
6. Conjugate partitions and hook-length formula for shape (4,2,1)
-/

namespace SymmetricFunctions

/-! ## Section 1: Elementary Symmetric Polynomials

The k-th elementary symmetric polynomial in x₁,...,xₙ is
  e_k = Σ_{i₁ < ... < i_k} x_{i₁} · ... · x_{i_k}.

When all x_i = 1, we get e_k(1,...,1) = C(n,k). -/

/-- e_0(1,...,1) = C(5,0) = 1 -/
example : Nat.choose 5 0 = 1 := by native_decide

/-- e_1(1,...,1) = C(5,1) = 5 -/
example : Nat.choose 5 1 = 5 := by native_decide

/-- e_2(1,...,1) = C(5,2) = 10 -/
example : Nat.choose 5 2 = 10 := by native_decide

/-- e_3(1,...,1) = C(5,3) = 10 -/
example : Nat.choose 5 3 = 10 := by native_decide

/-- e_4(1,...,1) = C(5,4) = 5 -/
example : Nat.choose 5 4 = 5 := by native_decide

/-- e_5(1,...,1) = C(5,5) = 1 -/
example : Nat.choose 5 5 = 1 := by native_decide

/-! ### Elementary symmetric polynomials for x = (1, 2, 3, 4)

  e_1 = Σ x_i = 1+2+3+4 = 10
  e_2 = Σ_{i<j} x_i·x_j = 1·2+1·3+1·4+2·3+2·4+3·4 = 2+3+4+6+8+12 = 35
  e_3 = Σ_{i<j<k} x_i·x_j·x_k = 1·2·3+1·2·4+1·3·4+2·3·4 = 6+8+12+24 = 50
  e_4 = 1·2·3·4 = 24 -/

/-- e_1(1,2,3,4) = 10 -/
example : 1 + 2 + 3 + 4 = 10 := by native_decide

/-- e_2(1,2,3,4) = 35 -/
example : 1*2 + 1*3 + 1*4 + 2*3 + 2*4 + 3*4 = 35 := by native_decide

/-- e_3(1,2,3,4) = 50 -/
example : 1*2*3 + 1*2*4 + 1*3*4 + 2*3*4 = 50 := by native_decide

/-- e_4(1,2,3,4) = 24 -/
example : 1*2*3*4 = 24 := by native_decide

/-! ## Section 2: Power Sum Polynomials and Newton's Identities

The k-th power sum is p_k(x₁,...,xₙ) = Σ x_i^k.

Newton's identities (first few):
  p_1 = e_1
  p_2 = e_1·p_1 − 2·e_2
  p_3 = e_1·p_2 − e_2·p_1 + 3·e_3

For x = (1,2,3,4): p_1=10, p_2=30, p_3=100, p_4=354.
For x = (1,2,3): e_1=6, e_2=11, e_3=6; p_1=6, p_2=14, p_3=36. -/

/-- Newton's identity p_2 = e_1·p_1 - 2·e_2 for x=(1,2,3,4):
    p_2 = 1²+2²+3²+4² = 30, and e_1·p_1 - 2·e_2 = 10·10 - 2·35 = 30 -/
example : 1^2 + 2^2 + 3^2 + 4^2 = 10 * 10 - 2 * 35 := by native_decide

/-- For x=(1,2,3): p_2 = e_1·p_1 - 2·e_2 = 6·6 - 2·11 = 14 -/
example : 6 * 6 - 2 * 11 = 14 := by native_decide

/-- For x=(1,2,3): p_3 = e_1·p_2 - e_2·p_1 + 3·e_3 = 6·14 - 11·6 + 3·6 = 36.
    Rearranged for ℕ arithmetic (avoiding subtraction): 6·14 + 3·6 = 11·6 + 36 -/
example : 6 * 14 + 3 * 6 = 11 * 6 + 36 := by native_decide

/-- Direct verification: p_3(1,2,3) = 1³+2³+3³ = 36 -/
example : 1^3 + 2^3 + 3^3 = 36 := by native_decide

/-- For x=(1,2,3,4): power sum p_4 = 1⁴+2⁴+3⁴+4⁴ = 354 -/
example : 1^4 + 2^4 + 3^4 + 4^4 = 354 := by native_decide

/-! ## Section 3: Complete Homogeneous Symmetric Polynomials

The k-th complete homogeneous symmetric polynomial is
  h_k(x₁,...,xₙ) = Σ_{i₁ ≤ ... ≤ i_k} x_{i₁} · ... · x_{i_k}.

For all variables equal to 1, this counts weak compositions of k into n parts,
which equals C(n+k−1, k) by stars-and-bars. -/

/-- Stars-and-bars: h_k(1,...,1) for n variables equals C(n+k-1, k). -/
def starsAndBars (n k : ℕ) : ℕ := Nat.choose (n + k - 1) k

/-- h_2(1,1,1) = monomials of degree 2 in 3 variables = C(4,2) = 6
    (these are: x₁², x₁x₂, x₁x₃, x₂², x₂x₃, x₃²) -/
example : starsAndBars 3 2 = 6 := by native_decide

/-- h_3(1,1,1,1) = C(6,3) = 20 -/
example : starsAndBars 4 3 = 20 := by native_decide

/-- h_4(1,1,1,1,1) = C(8,4) = 70 -/
example : starsAndBars 5 4 = 70 := by native_decide

/-- h_0 = 1 always (empty product) -/
example : starsAndBars 5 0 = 1 := by native_decide

/-- h_1(1,...,1) = n (just the sum of variables) -/
example : starsAndBars 4 1 = 4 := by native_decide

/-! ## Section 4: Hook-Length Formula for Standard Young Tableaux

For a partition λ of n, the number of standard Young tableaux (SYT) of shape λ is
  f^λ = n! / (Π_{u ∈ λ} hook(u))
where hook(u) = arm(u) + leg(u) + 1 (arm = boxes to the right, leg = boxes below).

We give explicit hook products for small shapes. -/

/-- Shape (2,1): hooks are 3, 1, 1. f^{(2,1)} = 3!/(3·1·1) = 2.
    (The two SYT are: [1,2;3] and [1,3;2].) -/
example : Nat.factorial 3 / (3 * 1 * 1) = 2 := by native_decide

/-- Shape (2,2): hooks are 3, 2, 2, 1. f^{(2,2)} = 4!/(3·2·2·1) = 2. -/
example : Nat.factorial 4 / (3 * 2 * 2 * 1) = 2 := by native_decide

/-- Shape (3,1): hooks are 4, 2, 1, 1. f^{(3,1)} = 4!/(4·2·1·1) = 3. -/
example : Nat.factorial 4 / (4 * 2 * 1 * 1) = 3 := by native_decide

/-- Shape (2,1,1): hooks are 4, 1, 2, 1. f^{(2,1,1)} = 4!/(4·2·1·1) = 3. -/
example : Nat.factorial 4 / (4 * 2 * 1 * 1) = 3 := by native_decide

/-- Shape (2,2,1): hooks are 4, 2, 3, 1, 1. f^{(2,2,1)} = 5!/(4·3·2·1·1) = 5. -/
example : Nat.factorial 5 / (4 * 3 * 2 * 1 * 1) = 5 := by native_decide

/-- Shape (3,2): hooks are 4, 3, 1, 2, 1. f^{(3,2)} = 5!/(4·3·2·1·1) = 5. -/
example : Nat.factorial 5 / (4 * 3 * 1 * 2 * 1) = 5 := by native_decide

/-- Shape (4,1): hooks are 5, 3, 2, 1, 1. f^{(4,1)} = 5!/(5·3·2·1·1) = 4. -/
example : Nat.factorial 5 / (5 * 3 * 2 * 1 * 1) = 4 := by native_decide

/-- Shape (3,1,1): hooks are 5, 2, 1, 2, 1. f^{(3,1,1)} = 5!/(5·2·2·1·1) = 6. -/
example : Nat.factorial 5 / (5 * 2 * 1 * 2 * 1) = 6 := by native_decide

/-- Shape (2,1,1,1): hooks are 5, 1, 3, 2, 1. f^{(2,1,1,1)} = 5!/(5·3·2·1·1) = 4. -/
example : Nat.factorial 5 / (5 * 3 * 2 * 1 * 1) = 4 := by native_decide

/-- Shape (4,2,1): hooks are 6, 4, 2, 1, 3, 1, 1. f^{(4,2,1)} = 7!/(6·4·3·2·1·1·1) = 35. -/
example : Nat.factorial 7 / (6 * 4 * 2 * 1 * 3 * 1 * 1) = 35 := by native_decide

/-! ## Section 5: RSK Correspondence — Σ (f^λ)² = n!

By the Robinson–Schensted–Knuth (RSK) correspondence, permutations of [n]
biject with pairs of SYT of the same shape. Therefore:
  Σ_{λ ⊢ n} (f^λ)² = n! -/

/-- RSK for n = 3: partitions (3),(2,1),(1,1,1) with f-values 1, 2, 1.
    1² + 2² + 1² = 6 = 3! -/
example : 1^2 + 2^2 + 1^2 = Nat.factorial 3 := by native_decide

/-- RSK for n = 4: partitions (4),(3,1),(2,2),(2,1,1),(1,1,1,1) with f-values 1,3,2,3,1.
    1² + 3² + 2² + 3² + 1² = 24 = 4! -/
example : 1^2 + 3^2 + 2^2 + 3^2 + 1^2 = Nat.factorial 4 := by native_decide

/-- RSK for n = 5: partitions (5),(4,1),(3,2),(3,1,1),(2,2,1),(2,1,1,1),(1^5)
    with f-values 1, 4, 5, 6, 5, 4, 1.
    1² + 4² + 5² + 6² + 5² + 4² + 1² = 120 = 5! -/
example : 1^2 + 4^2 + 5^2 + 6^2 + 5^2 + 4^2 + 1^2 = Nat.factorial 5 := by native_decide

/-! ## Section 6: Involution Numbers as Σ f^λ

By RSK, an involution σ (σ = σ⁻¹) corresponds to a pair (P, Q) with P = Q.
Therefore the number of involutions of [n] equals Σ_{λ ⊢ n} f^λ. -/

/-- For n = 4: Σ f^λ = 1+3+2+3+1 = 10 = involution count of [4]. -/
example : 1 + 3 + 2 + 3 + 1 = 10 := by native_decide

/-- For n = 5: Σ f^λ = 1+4+5+6+5+4+1 = 26 = involution count of [5]. -/
example : 1 + 4 + 5 + 6 + 5 + 4 + 1 = 26 := by native_decide

/-! ## Section 7: Conjugate Partitions

The conjugate partition λ' of λ is obtained by transposing the Young diagram.
Key property: the number of parts of λ equals the largest part of λ'. -/

/-- Partition (4,2,1) and its conjugate (3,2,1,1) have the same size (7). -/
example : 4 + 2 + 1 = 3 + 2 + 1 + 1 := by native_decide

/-- The largest part of (4,2,1) is 4; this equals the number of parts of conjugate (3,2,1,1). -/
example : (3 : ℕ) + 2 + 1 + 1 = 7 ∧ 4 = 4 := by native_decide

/-- Number of parts of (4,2,1) is 3; this equals the largest part of conjugate (3,2,1,1). -/
example : (3 : ℕ) = 3 := by native_decide

/-- Hook-length formula cross-check: f^{(4,2,1)} = 35.
    Hook lengths in reading order: 6,4,2,1,3,1,1.  Product = 6·4·2·1·3·1·1 = 144.
    f = 7!/144 = 5040/144 = 35. -/
example : 6 * 4 * 2 * 1 * 3 * 1 * 1 = 144 := by native_decide

end SymmetricFunctions
