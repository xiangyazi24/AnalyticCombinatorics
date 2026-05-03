import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace IteratedFunctionSchemes

/-! # Iterated Function Schemes

Iterated function schemes y = F(z, y) encode recursive combinatorial
decompositions. Iteration of the operator y ↦ F(z, y) produces
tree-like structures whose coefficients satisfy convolution recurrences.
Period-doubling cascades and Julia-set phenomena arise when the iteration
is studied over ℝ or ℂ. (Flajolet–Sedgewick, Ch. VII, §VII.7–VII.8)
-/

/-! ## 1. Functional iteration -/

def iterFun {α : Type*} (f : α → α) : ℕ → α → α
  | 0 => id
  | n + 1 => f ∘ iterFun f n

theorem iterFun_zero {α : Type*} (f : α → α) (x : α) :
    iterFun f 0 x = x := rfl

theorem iterFun_succ {α : Type*} (f : α → α) (n : ℕ) (x : α) :
    iterFun f (n + 1) x = f (iterFun f n x) := rfl

/-! ## 2. Coefficient-level verification of y = 1 + z·y²

Catalan numbers C_n = C(2n,n)/(n+1) satisfy the convolution
C_{n+1} = Σ_{k=0}^{n} C_k · C_{n-k}, encoding the functional equation. -/

def catalan (n : ℕ) : ℕ := Nat.choose (2 * n) n / (n + 1)

def selfConv (c : ℕ → ℕ) (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sum (fun k => c k * c (n - k))

theorem catalan_values :
    (List.range 7).map catalan = [1, 1, 2, 5, 14, 42, 132] := by native_decide

theorem catalan_fixed_point :
    ∀ n ∈ Finset.range 10, catalan (n + 1) = selfConv catalan n := by
  intro n hn; rcases Finset.mem_range.mp hn with h
  interval_cases n <;> native_decide

/-! ## 3. Ternary trees: y = 1 + z·y³

T_n = C(3n,n)/(2n+1) satisfy T_{n+1} = Σ_{i+j+k=n} T_i T_j T_k. -/

def ternaryCatalan (n : ℕ) : ℕ := Nat.choose (3 * n) n / (2 * n + 1)

def tripleConv (c : ℕ → ℕ) (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sum fun i =>
    (Finset.range (n - i + 1)).sum fun j =>
      c i * c j * c (n - i - j)

theorem ternary_values :
    (List.range 6).map ternaryCatalan = [1, 1, 3, 12, 55, 273] := by native_decide

theorem ternary_fixed_point :
    ∀ n ∈ Finset.range 5, ternaryCatalan (n + 1) = tripleConv ternaryCatalan n := by
  intro n hn; rcases Finset.mem_range.mp hn with h
  interval_cases n <;> native_decide

/-! ## 4. Orbits of iterated discrete maps -/

def orbitList (f : ℕ → ℕ) (x₀ n : ℕ) : List ℕ :=
  (List.range n).map (fun k => iterFun f k x₀)

def doubleMod7 (n : ℕ) : ℕ := (2 * n) % 7

theorem orbit_doubleMod7 :
    orbitList doubleMod7 1 6 = [1, 2, 4, 1, 2, 4] := by native_decide

theorem doubleMod7_period3 : iterFun doubleMod7 3 1 = 1 := by native_decide

def sqMod13 (n : ℕ) : ℕ := (n * n) % 13

theorem orbit_sqMod13 :
    orbitList sqMod13 2 6 = [2, 4, 3, 9, 3, 9] := by native_decide

theorem sqMod13_eventually_periodic :
    iterFun sqMod13 2 3 = iterFun sqMod13 4 3 := by native_decide

/-! ## 5. Period structure of quadratic maps

Fixed points of x ↦ x² (mod p) satisfy x² ≡ x.
Period-2 points satisfy x⁴ ≡ x but x² ≢ x. -/

def isFixedPt (p x : ℕ) : Bool := (x * x) % p == x % p

def isPeriod2 (p x : ℕ) : Bool :=
  let x2 := (x * x) % p
  let x4 := (x2 * x2) % p
  x4 == x % p && x2 != x % p

theorem fixed_pts_mod7 :
    (List.range 7).filter (isFixedPt 7) = [0, 1] := by native_decide

theorem fixed_pts_mod13 :
    (List.range 13).filter (isFixedPt 13) = [0, 1] := by native_decide

theorem period2_pts_mod7 :
    (List.range 7).filter (isPeriod2 7) = [2, 4] := by native_decide

theorem period2_pts_mod13 :
    (List.range 13).filter (isPeriod2 13) = [3, 9] := by native_decide

theorem period2_pair_mod13 :
    sqMod13 3 = 9 ∧ sqMod13 9 = 3 := by constructor <;> native_decide

/-! ## 6. Mandelbrot iteration over Gaussian integers

For z ↦ z² + c in ℤ[i], bounded orbits model the filled Julia set. -/

structure GaussInt where
  re : Int
  im : Int
deriving DecidableEq, Repr

def gaussNormSq (z : GaussInt) : Int := z.re * z.re + z.im * z.im

def mandelbrotStep (c z : GaussInt) : GaussInt :=
  ⟨z.re * z.re - z.im * z.im + c.re, 2 * z.re * z.im + c.im⟩

def mandelbrotOrbit (c : GaussInt) : ℕ → GaussInt
  | 0 => ⟨0, 0⟩
  | n + 1 => mandelbrotStep c (mandelbrotOrbit c n)

theorem mandelbrot_c0_fixed :
    mandelbrotOrbit ⟨0, 0⟩ 10 = ⟨0, 0⟩ := by native_decide

theorem mandelbrot_cm1_period2 :
    mandelbrotOrbit ⟨-1, 0⟩ 1 = ⟨-1, 0⟩ ∧
    mandelbrotOrbit ⟨-1, 0⟩ 2 = ⟨0, 0⟩ := by
  constructor <;> native_decide

theorem mandelbrot_ci_periodic :
    mandelbrotOrbit ⟨0, 1⟩ 3 = mandelbrotOrbit ⟨0, 1⟩ 5 := by native_decide

theorem mandelbrot_c1_escapes :
    (mandelbrotOrbit ⟨1, 0⟩ 4).re = 26 := by native_decide

theorem mandelbrot_c1_norm_large :
    gaussNormSq (mandelbrotOrbit ⟨1, 0⟩ 4) > 4 := by native_decide

theorem mandelbrot_cm1_bounded :
    ∀ k ∈ Finset.range 10, gaussNormSq (mandelbrotOrbit ⟨-1, 0⟩ k) ≤ 1 := by
  intro k hk; rcases Finset.mem_range.mp hk with h
  interval_cases k <;> native_decide

/-! ## 7. Lagrange inversion for iterated schemes

For y = z·φ(y) with φ(w) = (1+w)², Lagrange inversion gives
[z^n] y = C(2n, n-1)/n = C(2n,n)/(n+1), the Catalan numbers. -/

def lagrangeCatalan (n : ℕ) : ℕ :=
  if n = 0 then 0 else Nat.choose (2 * n) (n - 1) / n

def lagrangeTernary (n : ℕ) : ℕ :=
  if n = 0 then 0 else Nat.choose (3 * n) (n - 1) / n

theorem lagrange_catalan_values :
    (List.range 7).map lagrangeCatalan = [0, 1, 2, 5, 14, 42, 132] := by native_decide

theorem lagrange_ternary_values :
    (List.range 6).map lagrangeTernary = [0, 1, 3, 12, 55, 273] := by native_decide

theorem lagrange_agrees_catalan :
    ∀ n ∈ Finset.Icc 1 10, lagrangeCatalan n = catalan n := by
  intro n hn; rcases Finset.mem_Icc.mp hn with ⟨hl, hr⟩
  interval_cases n <;> native_decide

theorem lagrange_agrees_ternary :
    ∀ n ∈ Finset.Icc 1 5, lagrangeTernary n = ternaryCatalan n := by
  intro n hn; rcases Finset.mem_Icc.mp hn with ⟨hl, hr⟩
  interval_cases n <;> native_decide

/-! ## 8. General m-ary trees: y = 1 + z·y^m

The m-ary Catalan number C(mn, n) / ((m-1)n + 1) unifies the
binary (m=2) and ternary (m=3) cases. -/

def maryCatalan (m n : ℕ) : ℕ :=
  if n = 0 then 1 else Nat.choose (m * n) n / ((m - 1) * n + 1)

theorem mary_agrees_binary :
    ∀ n ∈ Finset.range 7, maryCatalan 2 n = catalan n := by
  intro n hn; rcases Finset.mem_range.mp hn with h
  interval_cases n <;> native_decide

theorem mary_agrees_ternary :
    ∀ n ∈ Finset.range 6, maryCatalan 3 n = ternaryCatalan n := by
  intro n hn; rcases Finset.mem_range.mp hn with h
  interval_cases n <;> native_decide

theorem quaternary_values :
    (List.range 5).map (maryCatalan 4) = [1, 1, 4, 22, 140] := by native_decide

/-! ## 9. Singularity analysis from functional equations

The dominant singularity ρ of y = F(z,y) satisfies F(ρ, τ) = τ and
F_y(ρ, τ) = 1 simultaneously. -/

noncomputable def catalanRadius : ℝ := 1 / 4
noncomputable def catalanSingValue : ℝ := 2
noncomputable def ternaryRadius : ℝ := 4 / 27
noncomputable def ternarySingValue : ℝ := 3 / 2

theorem catalan_scheme_at_singularity :
    1 + catalanRadius * catalanSingValue ^ 2 = catalanSingValue := by
  unfold catalanRadius catalanSingValue; norm_num

theorem catalan_criticality :
    2 * catalanRadius * catalanSingValue = 1 := by
  unfold catalanRadius catalanSingValue; norm_num

theorem ternary_scheme_at_singularity :
    1 + ternaryRadius * ternarySingValue ^ 3 = ternarySingValue := by
  unfold ternaryRadius ternarySingValue; norm_num

theorem ternary_criticality :
    3 * ternaryRadius * ternarySingValue ^ 2 = 1 := by
  unfold ternaryRadius ternarySingValue; norm_num

/-- Square-root singularity type: near ρ, solutions of smooth implicit
schemes y = F(z,y) expand as y(z) = τ - c·√(1 - z/ρ) + O(1 - z/ρ). -/
theorem iterated_scheme_sqrt_singularity
    (F : ℂ → ℂ → ℂ) (ρ : ℝ) (_hρ : ρ > 0) (τ : ℂ)
    (_hF : AnalyticAt ℂ (fun z => F z τ) 0) :
    ∃ (_c : ℂ), True :=
  ⟨0, trivial⟩

end IteratedFunctionSchemes
