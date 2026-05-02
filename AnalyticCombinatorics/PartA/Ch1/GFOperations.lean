/-
  Chapter I — Generating Function Operations

  Basic operations on generating functions (as coefficient sequences ℕ → ℕ):
  • Hadamard product (coefficient-wise multiplication)
  • SEQ construction (compositions counting)
  • Integer partition counts (MSET construction)
  • Distinct-part partition counts (PSET construction)
  • Cauchy product (convolution)

  Reference: Flajolet & Sedgewick, Analytic Combinatorics, Chapter I.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

open Finset

namespace GFOperations

/-! ## Hadamard Product -/

/-- Coefficient-wise (Hadamard) product of two sequences. -/
def hadamardProduct (f g : ℕ → ℕ) : ℕ → ℕ := fun n => f n * g n

theorem hadamard_exp_linear_0 :
    hadamardProduct (fun n => 2^n) (fun n => n + 1) 0 = 1 := by native_decide

theorem hadamard_exp_linear_1 :
    hadamardProduct (fun n => 2^n) (fun n => n + 1) 1 = 4 := by native_decide

theorem hadamard_exp_linear_2 :
    hadamardProduct (fun n => 2^n) (fun n => n + 1) 2 = 12 := by native_decide

theorem hadamard_exp_linear_3 :
    hadamardProduct (fun n => 2^n) (fun n => n + 1) 3 = 32 := by native_decide

theorem hadamard_exp_linear_4 :
    hadamardProduct (fun n => 2^n) (fun n => n + 1) 4 = 80 := by native_decide

/-! ## SEQ Construction (Compositions) -/

/-- Number of compositions of n: 1 for n=0, 2^(n-1) for n≥1.
    If B(z) = z/(1-z) (b_n = 1 for n≥1), then SEQ(B) has OGF
    1/(1 - z/(1-z)) = (1-z)/(1-2z), giving these coefficients. -/
def seqCount (n : ℕ) : ℕ := if n = 0 then 1 else 2^(n-1)

theorem seqCount_0 : seqCount 0 = 1 := by native_decide
theorem seqCount_1 : seqCount 1 = 1 := by native_decide
theorem seqCount_2 : seqCount 2 = 2 := by native_decide
theorem seqCount_3 : seqCount 3 = 4 := by native_decide
theorem seqCount_4 : seqCount 4 = 8 := by native_decide
theorem seqCount_5 : seqCount 5 = 16 := by native_decide
theorem seqCount_6 : seqCount 6 = 32 := by native_decide
theorem seqCount_7 : seqCount 7 = 64 := by native_decide
theorem seqCount_8 : seqCount 8 = 128 := by native_decide

/-! ## Integer Partition Count (MSET construction) -/

/-- Table of partition numbers p(0)..p(10). -/
def partitionTable : Fin 11 → ℕ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 2
  | ⟨3, _⟩ => 3
  | ⟨4, _⟩ => 5
  | ⟨5, _⟩ => 7
  | ⟨6, _⟩ => 11
  | ⟨7, _⟩ => 15
  | ⟨8, _⟩ => 22
  | ⟨9, _⟩ => 30
  | ⟨10, _⟩ => 42

/-- Sum of divisors function σ₁(n). -/
def sigma1 (n : ℕ) : ℕ :=
  (Finset.filter (· ∣ n) (Finset.range (n + 1))).sum id

theorem sigma1_1 : sigma1 1 = 1 := by native_decide
theorem sigma1_2 : sigma1 2 = 3 := by native_decide
theorem sigma1_3 : sigma1 3 = 4 := by native_decide
theorem sigma1_4 : sigma1 4 = 7 := by native_decide
theorem sigma1_6 : sigma1 6 = 12 := by native_decide

/-- Recursive partition count using the sigma recurrence:
    p(0) = 1, (n+1)*p(n+1) = Σ_{k=1}^{n+1} σ₁(k) * p(n+1-k). -/
def partitionRec : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
    let s := (Finset.range (n + 1)).sum (fun k => sigma1 (k + 1) * partitionRec (n - k))
    s / (n + 1)

theorem partitionRec_0 : partitionRec 0 = 1 := by native_decide
theorem partitionRec_1 : partitionRec 1 = 1 := by native_decide
theorem partitionRec_2 : partitionRec 2 = 2 := by native_decide
theorem partitionRec_3 : partitionRec 3 = 3 := by native_decide
theorem partitionRec_4 : partitionRec 4 = 5 := by native_decide
theorem partitionRec_5 : partitionRec 5 = 7 := by native_decide
theorem partitionRec_6 : partitionRec 6 = 11 := by native_decide
theorem partitionRec_7 : partitionRec 7 = 15 := by native_decide
theorem partitionRec_8 : partitionRec 8 = 22 := by native_decide
theorem partitionRec_9 : partitionRec 9 = 30 := by native_decide
theorem partitionRec_10 : partitionRec 10 = 42 := by native_decide

/-- The recursive computation matches the hardcoded table. -/
theorem partitionRec_matches_table :
    ∀ i : Fin 11, partitionRec i.val = partitionTable i := by native_decide

/-! ## Distinct-Part Partition Count (PSET construction) -/

/-- Number of partitions of n into distinct parts.
    Uses the recurrence: q(n) = Σ_{k=1}^{n} (-1)^{k+1} * q(n-k) where terms
    contribute only at triangular numbers, but we use a direct table here. -/
def distinctPartTable : Fin 9 → ℕ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 2
  | ⟨4, _⟩ => 2
  | ⟨5, _⟩ => 3
  | ⟨6, _⟩ => 4
  | ⟨7, _⟩ => 5
  | ⟨8, _⟩ => 6

/-- Distinct-part partition count via direct enumeration.
    Count the number of subsets of {1,...,n} that sum to n. -/
def distinctPartCount (n : ℕ) : ℕ :=
  ((Finset.range n).powerset.filter
    (fun s => (s.sum (· + 1)) = n)).card

theorem distinctPartCount_0 : distinctPartCount 0 = 1 := by native_decide
theorem distinctPartCount_1 : distinctPartCount 1 = 1 := by native_decide
theorem distinctPartCount_2 : distinctPartCount 2 = 1 := by native_decide
theorem distinctPartCount_3 : distinctPartCount 3 = 2 := by native_decide
theorem distinctPartCount_4 : distinctPartCount 4 = 2 := by native_decide
theorem distinctPartCount_5 : distinctPartCount 5 = 3 := by native_decide
theorem distinctPartCount_6 : distinctPartCount 6 = 4 := by native_decide
theorem distinctPartCount_7 : distinctPartCount 7 = 5 := by native_decide
theorem distinctPartCount_8 : distinctPartCount 8 = 6 := by native_decide

/-- The computed values match the hardcoded table. -/
theorem distinctPartCount_matches_table :
    ∀ i : Fin 9, distinctPartCount i.val = distinctPartTable i := by native_decide

/-! ## Cauchy Product (Convolution) -/

/-- Cauchy product (convolution) of two coefficient sequences. -/
def cauchyProduct (f g : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), f k * g (n - k)

/-- Convolving the constant-1 sequence with itself gives n+1
    (coefficients of 1/(1-z)^2). -/
theorem cauchy_ones_0 :
    cauchyProduct (fun _ => 1) (fun _ => 1) 0 = 1 := by native_decide

theorem cauchy_ones_1 :
    cauchyProduct (fun _ => 1) (fun _ => 1) 1 = 2 := by native_decide

theorem cauchy_ones_2 :
    cauchyProduct (fun _ => 1) (fun _ => 1) 2 = 3 := by native_decide

theorem cauchy_ones_3 :
    cauchyProduct (fun _ => 1) (fun _ => 1) 3 = 4 := by native_decide

theorem cauchy_ones_4 :
    cauchyProduct (fun _ => 1) (fun _ => 1) 4 = 5 := by native_decide

theorem cauchy_ones_5 :
    cauchyProduct (fun _ => 1) (fun _ => 1) 5 = 6 := by native_decide

/-- The Cauchy product 1*1 gives n+1 for small n. -/
theorem cauchy_ones_eq_succ :
    ∀ n ∈ Finset.range 6,
      cauchyProduct (fun _ => 1) (fun _ => 1) n = n + 1 := by native_decide

end GFOperations
