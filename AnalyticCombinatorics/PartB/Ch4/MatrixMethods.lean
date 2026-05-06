import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch4.MatrixMethods


/-!
Chapter IV matrix-method checks.

All statements below are finite, executable verifications.  They model the
transfer-matrix viewpoint used for rational generating functions: entries of
matrix powers count walks, traces count closed walks, and companion matrices
encode linear recurrences.
-/

abbrev NatMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℕ
abbrev IntMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℤ

def transferTrace {n : ℕ} (A : NatMatrix n) (k : ℕ) : ℕ :=
  Matrix.trace (A ^ k)

def walkCount {n : ℕ} (A : NatMatrix n) (k : ℕ) (i j : Fin n) : ℕ :=
  (A ^ k) i j

/-! ## 1. Transfer matrix for paths -/

def edgeGraph : NatMatrix 2 :=
  !![0, 1;
     1, 0]

def triangleGraph : NatMatrix 3 :=
  !![0, 1, 1;
     1, 0, 1;
     1, 1, 0]

-- The trace of A^0 counts one length-zero closed path at each vertex.
example : transferTrace edgeGraph 0 = 2 := by native_decide

-- A single edge graph has no closed paths of odd length.
example : transferTrace edgeGraph 1 = 0 := by native_decide
example : transferTrace edgeGraph 3 = 0 := by native_decide

-- Its two length-two closed paths are 0 -> 1 -> 0 and 1 -> 0 -> 1.
example : transferTrace edgeGraph 2 = 2 := by native_decide

-- In the triangle, each vertex has two length-two closed walks.
example : transferTrace triangleGraph 2 = 6 := by native_decide

-- The six directed length-three closed walks go around the triangle.
example : transferTrace triangleGraph 3 = 6 := by native_decide

/-! ## 2. Fibonacci via matrix exponentiation -/

def fibMatrix : NatMatrix 2 :=
  !![1, 1;
     1, 0]

def fibPowerShape (n : ℕ) : NatMatrix 2 :=
  !![Nat.fib (n + 1), Nat.fib n;
     Nat.fib n, Nat.fib (n - 1)]

example : fibMatrix ^ 1 = fibPowerShape 1 := by native_decide
example : fibMatrix ^ 2 = fibPowerShape 2 := by native_decide
example : fibMatrix ^ 3 = fibPowerShape 3 := by native_decide
example : fibMatrix ^ 4 = fibPowerShape 4 := by native_decide
example : fibMatrix ^ 5 = fibPowerShape 5 := by native_decide
example : fibMatrix ^ 6 = fibPowerShape 6 := by native_decide
example : fibMatrix ^ 7 = fibPowerShape 7 := by native_decide
example : fibMatrix ^ 8 = fibPowerShape 8 := by native_decide

example : (fibMatrix ^ 10) 0 1 = Nat.fib 10 := by native_decide
example : (fibMatrix ^ 10) 0 0 = Nat.fib 11 := by native_decide
example : Matrix.trace (fibMatrix ^ 6) = Nat.fib 7 + Nat.fib 5 := by native_decide

/-! ## 3. Adjacency matrix powers for complete graphs -/

def completeGraph3 : NatMatrix 3 :=
  !![0, 1, 1;
     1, 0, 1;
     1, 1, 0]

def completeGraph4 : NatMatrix 4 :=
  !![0, 1, 1, 1;
     1, 0, 1, 1;
     1, 1, 0, 1;
     1, 1, 1, 0]

-- For K_3, A^2 has diagonal entries 2 and off-diagonal entries 1.
example : walkCount completeGraph3 2 0 0 = 2 := by native_decide
example : walkCount completeGraph3 2 0 1 = 1 := by native_decide
example : walkCount completeGraph3 2 1 2 = 1 := by native_decide

-- For K_3, A^3 has diagonal entries 2 and off-diagonal entries 3.
example : walkCount completeGraph3 3 0 0 = 2 := by native_decide
example : walkCount completeGraph3 3 0 1 = 3 := by native_decide
example : transferTrace completeGraph3 3 = 6 := by native_decide

-- For K_4, A^2 has diagonal entries 3 and off-diagonal entries 2.
example : walkCount completeGraph4 2 0 0 = 3 := by native_decide
example : walkCount completeGraph4 2 0 1 = 2 := by native_decide
example : walkCount completeGraph4 2 2 3 = 2 := by native_decide

-- For K_4, A^3 has diagonal entries 6 and off-diagonal entries 7.
example : walkCount completeGraph4 3 0 0 = 6 := by native_decide
example : walkCount completeGraph4 3 0 1 = 7 := by native_decide
example : transferTrace completeGraph4 3 = 24 := by native_decide

/-! ## 4. Characteristic roots and recurrences from a minimal polynomial -/

def minPoly23 (x : ℤ) : ℤ :=
  x ^ 2 - 5 * x + 6

def rootPower (r : ℤ) (n : ℕ) : ℤ :=
  r ^ n

def rootSum23 (n : ℕ) : ℤ :=
  rootPower 2 n + rootPower 3 n

def recurrence23Check (a : ℕ → ℤ) (n : ℕ) : Bool :=
  a (n + 2) == 5 * a (n + 1) - 6 * a n

example : minPoly23 2 = 0 := by native_decide
example : minPoly23 3 = 0 := by native_decide

-- Each root sequence r^n satisfies a(n+2) = 5 a(n+1) - 6 a(n).
example : recurrence23Check (rootPower 2) 0 = true := by native_decide
example : recurrence23Check (rootPower 2) 1 = true := by native_decide
example : recurrence23Check (rootPower 2) 2 = true := by native_decide
example : recurrence23Check (rootPower 2) 3 = true := by native_decide

example : recurrence23Check (rootPower 3) 0 = true := by native_decide
example : recurrence23Check (rootPower 3) 1 = true := by native_decide
example : recurrence23Check (rootPower 3) 2 = true := by native_decide
example : recurrence23Check (rootPower 3) 3 = true := by native_decide

-- Linear combinations of root sequences satisfy the same recurrence.
example : recurrence23Check rootSum23 0 = true := by native_decide
example : recurrence23Check rootSum23 1 = true := by native_decide
example : recurrence23Check rootSum23 2 = true := by native_decide
example : recurrence23Check rootSum23 3 = true := by native_decide
example : recurrence23Check rootSum23 4 = true := by native_decide

/-! ## 5. Cayley-Hamilton numerical checks for 2x2 matrices -/

def cayleyHamilton2 (A : IntMatrix 2) : IntMatrix 2 :=
  A ^ 2 - Matrix.trace A • A + Matrix.scalar (Fin 2) (Matrix.det A)

def intMatrixA : IntMatrix 2 :=
  !![1, 2;
     3, 4]

def intMatrixB : IntMatrix 2 :=
  !![0, 1;
     -2, 3]

def intMatrixC : IntMatrix 2 :=
  !![5, -1;
     2, 0]

example : Matrix.trace intMatrixA = 5 := by native_decide
example : Matrix.det intMatrixA = -2 := by native_decide
example : cayleyHamilton2 intMatrixA = 0 := by native_decide

example : Matrix.trace intMatrixB = 3 := by native_decide
example : Matrix.det intMatrixB = 2 := by native_decide
example : cayleyHamilton2 intMatrixB = 0 := by native_decide

example : Matrix.trace intMatrixC = 5 := by native_decide
example : Matrix.det intMatrixC = 2 := by native_decide
example : cayleyHamilton2 intMatrixC = 0 := by native_decide

/-! ## 6. Companion matrix of a linear recurrence -/

def companion2 (c1 c0 : ℤ) : IntMatrix 2 :=
  !![c1, c0;
     1, 0]

-- Coefficients are listed as constant, x, x^2.
def charPoly2Coeffs (A : IntMatrix 2) : Fin 3 → ℤ :=
  ![Matrix.det A, -Matrix.trace A, 1]

-- For a(n+2) = c1 a(n+1) + c0 a(n), the recurrence polynomial is
-- x^2 - c1*x - c0.
def recurrencePoly2Coeffs (c1 c0 : ℤ) : Fin 3 → ℤ :=
  ![-c0, -c1, 1]

example :
    charPoly2Coeffs (companion2 1 1) = recurrencePoly2Coeffs 1 1 := by
  native_decide

example :
    charPoly2Coeffs (companion2 3 (-2)) = recurrencePoly2Coeffs 3 (-2) := by
  native_decide

example :
    charPoly2Coeffs (companion2 5 (-6)) = recurrencePoly2Coeffs 5 (-6) := by
  native_decide

example :
    charPoly2Coeffs (companion2 2 1) = recurrencePoly2Coeffs 2 1 := by
  native_decide

def fibCompanionInt : IntMatrix 2 :=
  companion2 1 1

-- Fibonacci companion: x^2 - x - 1.
example : charPoly2Coeffs fibCompanionInt = ![-1, -1, 1] := by native_decide

-- The companion for a(n+2) = 5 a(n+1) - 6 a(n) has roots 2 and 3.
def recurrence56Companion : IntMatrix 2 :=
  companion2 5 (-6)

example : charPoly2Coeffs recurrence56Companion = ![6, -5, 1] := by native_decide
example : minPoly23 2 = 0 := by native_decide
example : minPoly23 3 = 0 := by native_decide

/-- Cayley-Hamilton check for the first integer matrix sample. -/
theorem cayleyHamilton2_intMatrixA :
    cayleyHamilton2 intMatrixA = 0 := by
  native_decide

/-- Companion matrix characteristic coefficients for the Fibonacci recurrence. -/
theorem charPoly2Coeffs_fibCompanionInt :
    charPoly2Coeffs fibCompanionInt = ![-1, -1, 1] := by
  native_decide



structure MatrixMethodsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MatrixMethodsBudgetCertificate.controlled
    (c : MatrixMethodsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def MatrixMethodsBudgetCertificate.budgetControlled
    (c : MatrixMethodsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def MatrixMethodsBudgetCertificate.Ready
    (c : MatrixMethodsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def MatrixMethodsBudgetCertificate.size
    (c : MatrixMethodsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem matrixMethods_budgetCertificate_le_size
    (c : MatrixMethodsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleMatrixMethodsBudgetCertificate :
    MatrixMethodsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleMatrixMethodsBudgetCertificate.Ready := by
  constructor
  · norm_num [MatrixMethodsBudgetCertificate.controlled,
      sampleMatrixMethodsBudgetCertificate]
  · norm_num [MatrixMethodsBudgetCertificate.budgetControlled,
      sampleMatrixMethodsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleMatrixMethodsBudgetCertificate.certificateBudgetWindow ≤
      sampleMatrixMethodsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleMatrixMethodsBudgetCertificate.Ready := by
  constructor
  · norm_num [MatrixMethodsBudgetCertificate.controlled,
      sampleMatrixMethodsBudgetCertificate]
  · norm_num [MatrixMethodsBudgetCertificate.budgetControlled,
      sampleMatrixMethodsBudgetCertificate]

example :
    sampleMatrixMethodsBudgetCertificate.certificateBudgetWindow ≤
      sampleMatrixMethodsBudgetCertificate.size := by
  apply matrixMethods_budgetCertificate_le_size
  constructor
  · norm_num [MatrixMethodsBudgetCertificate.controlled,
      sampleMatrixMethodsBudgetCertificate]
  · norm_num [MatrixMethodsBudgetCertificate.budgetControlled,
      sampleMatrixMethodsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List MatrixMethodsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleMatrixMethodsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleMatrixMethodsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch4.MatrixMethods
