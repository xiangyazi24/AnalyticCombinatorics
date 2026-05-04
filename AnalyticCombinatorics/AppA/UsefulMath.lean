import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Appendix A: Useful Mathematics

Small executable lemmas and finite certificates for the algebraic and
discrete tools used throughout analytic combinatorics.
-/

namespace AnalyticCombinatorics.AppA.UsefulMath

/-- Falling factorial `x (x-1) ... (x-k+1)` over natural inputs. -/
def fallingFactorial : ℕ → ℕ → ℕ
  | _, 0 => 1
  | n, k + 1 => (n - k) * fallingFactorial n k

/-- Rising factorial `x (x+1) ... (x+k-1)`. -/
def risingFactorial : ℕ → ℕ → ℕ
  | _, 0 => 1
  | n, k + 1 => (n + k) * risingFactorial n k

theorem fallingFactorial_zero (n : ℕ) : fallingFactorial n 0 = 1 := rfl

theorem risingFactorial_zero (n : ℕ) : risingFactorial n 0 = 1 := rfl

theorem fallingFactorial_succ (n k : ℕ) :
    fallingFactorial n (k + 1) = (n - k) * fallingFactorial n k := rfl

theorem risingFactorial_succ (n k : ℕ) :
    risingFactorial n (k + 1) = (n + k) * risingFactorial n k := rfl

theorem fallingFactorial_samples :
    fallingFactorial 6 0 = 1 ∧
    fallingFactorial 6 1 = 6 ∧
    fallingFactorial 6 2 = 30 ∧
    fallingFactorial 6 3 = 120 ∧
    fallingFactorial 6 4 = 360 := by
  native_decide

theorem risingFactorial_samples :
    risingFactorial 3 0 = 1 ∧
    risingFactorial 3 1 = 3 ∧
    risingFactorial 3 2 = 12 ∧
    risingFactorial 3 3 = 60 ∧
    risingFactorial 3 4 = 360 := by
  native_decide

/-- Signed first finite difference. -/
def firstDiff (a : ℕ → ℤ) (n : ℕ) : ℤ :=
  a (n + 1) - a n

/-- Signed second finite difference. -/
def secondDiff (a : ℕ → ℤ) (n : ℕ) : ℤ :=
  firstDiff a (n + 1) - firstDiff a n

def squareSeq (n : ℕ) : ℤ := (n : ℤ) ^ 2

def cubeSeq (n : ℕ) : ℤ := (n : ℤ) ^ 3

theorem square_firstDiff :
    firstDiff squareSeq 0 = 1 ∧
    firstDiff squareSeq 1 = 3 ∧
    firstDiff squareSeq 2 = 5 ∧
    firstDiff squareSeq 3 = 7 := by
  native_decide

theorem square_secondDiff_constant :
    secondDiff squareSeq 0 = 2 ∧
    secondDiff squareSeq 1 = 2 ∧
    secondDiff squareSeq 2 = 2 ∧
    secondDiff squareSeq 3 = 2 := by
  native_decide

theorem cube_secondDiff :
    secondDiff cubeSeq 0 = 6 ∧
    secondDiff cubeSeq 1 = 12 ∧
    secondDiff cubeSeq 2 = 18 ∧
    secondDiff cubeSeq 3 = 24 := by
  native_decide

/-- Finite check for log-convexity: `a_n^2 <= a_{n-1} a_{n+1}`. -/
def logConvexUpTo (a : ℕ → ℕ) (N : ℕ) : Bool :=
  (List.range N).all fun n =>
    if n = 0 then true else a n * a n ≤ a (n - 1) * a (n + 1)

def factorialSeq (n : ℕ) : ℕ := Nat.factorial n

theorem factorial_logConvex_10 :
    logConvexUpTo factorialSeq 10 = true := by
  native_decide

/-- Partial sums of a natural sequence. -/
def partialSum (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  (List.range (n + 1)).foldl (fun s k => s + a k) 0

theorem partialSum_linear :
    partialSum (fun n => n) 0 = 0 ∧
    partialSum (fun n => n) 1 = 1 ∧
    partialSum (fun n => n) 2 = 3 ∧
    partialSum (fun n => n) 3 = 6 ∧
    partialSum (fun n => n) 4 = 10 := by
  native_decide

theorem partialSum_geometric_two :
    partialSum (fun n => 2 ^ n) 0 = 1 ∧
    partialSum (fun n => 2 ^ n) 1 = 3 ∧
    partialSum (fun n => 2 ^ n) 2 = 7 ∧
    partialSum (fun n => 2 ^ n) 3 = 15 ∧
    partialSum (fun n => 2 ^ n) 4 = 31 := by
  native_decide

/-- Binomial transform of a finite prefix. -/
def binomialTransform (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  (List.range (n + 1)).foldl (fun s k => s + n.choose k * a k) 0

theorem binomialTransform_constant :
    binomialTransform (fun _ => 1) 0 = 1 ∧
    binomialTransform (fun _ => 1) 1 = 2 ∧
    binomialTransform (fun _ => 1) 2 = 4 ∧
    binomialTransform (fun _ => 1) 3 = 8 ∧
    binomialTransform (fun _ => 1) 4 = 16 := by
  native_decide

theorem binomialTransform_identity :
    binomialTransform (fun n => n) 0 = 0 ∧
    binomialTransform (fun n => n) 1 = 1 ∧
    binomialTransform (fun n => n) 2 = 4 ∧
    binomialTransform (fun n => n) 3 = 12 ∧
    binomialTransform (fun n => n) 4 = 32 := by
  native_decide

/-- Ordinary convolution of two finite prefixes. -/
def convolution (a b : ℕ → ℕ) (n : ℕ) : ℕ :=
  (List.range (n + 1)).foldl (fun s k => s + a k * b (n - k)) 0

theorem convolution_constant :
    convolution (fun _ => 1) (fun _ => 1) 0 = 1 ∧
    convolution (fun _ => 1) (fun _ => 1) 1 = 2 ∧
    convolution (fun _ => 1) (fun _ => 1) 2 = 3 ∧
    convolution (fun _ => 1) (fun _ => 1) 3 = 4 ∧
    convolution (fun _ => 1) (fun _ => 1) 4 = 5 := by
  native_decide

theorem convolution_geometric :
    convolution (fun n => 2 ^ n) (fun _ => 1) 0 = 1 ∧
    convolution (fun n => 2 ^ n) (fun _ => 1) 1 = 3 ∧
    convolution (fun n => 2 ^ n) (fun _ => 1) 2 = 7 ∧
    convolution (fun n => 2 ^ n) (fun _ => 1) 3 = 15 ∧
    convolution (fun n => 2 ^ n) (fun _ => 1) 4 = 31 := by
  native_decide

end AnalyticCombinatorics.AppA.UsefulMath
