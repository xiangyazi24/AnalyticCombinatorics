import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartA.Ch2.DesignTheory


/-! # Combinatorial Design Theory (Ch II / Appendix)

Numerical verifications for classical results on BIBD parameters,
Steiner triple systems, Latin squares, Hadamard matrices, projective planes,
and Ramsey numbers.
-/

-- ════════════════════════════════════════════════════════════════════
-- § 1. BIBD parameters (b, v, r, k, λ)
-- ════════════════════════════════════════════════════════════════════

/-- Fano plane (7,3,1)-design: b = λv(v-1)/(k(k-1)) = 7. -/
example : 1 * 7 * 6 / (3 * 2) = 7 := by native_decide

/-- Fano plane: r = λ(v-1)/(k-1) = 3. -/
example : 1 * 6 / 2 = 3 := by native_decide

/-- (11,5,2)-design: b = 2·11·10/(5·4) = 11. -/
example : 2 * 11 * 10 / (5 * 4) = 11 := by native_decide

/-- (11,5,2)-design: r = 2·10/4 = 5. -/
example : 2 * 10 / 4 = 5 := by native_decide

/-- Fisher's inequality for Fano: b ≥ v. -/
example : (7 : ℕ) ≥ 7 := by native_decide

/-- Fisher's inequality for (11,5,2): b ≥ v (symmetric design). -/
example : (11 : ℕ) ≥ 11 := by native_decide

-- ════════════════════════════════════════════════════════════════════
-- § 2. Steiner triple systems S(2,3,v)
-- ════════════════════════════════════════════════════════════════════

/-- S(2,3,7): number of blocks = v(v-1)/6 = 7. -/
example : 7 * 6 / 6 = 7 := by native_decide

/-- S(2,3,9): number of blocks = 12. -/
example : 9 * 8 / 6 = 12 := by native_decide

/-- S(2,3,13): number of blocks = 26. -/
example : 13 * 12 / 6 = 26 := by native_decide

/-- Existence condition: v ≡ 1 (mod 6) for v=7. -/
example : 7 % 6 = 1 := by native_decide

/-- Existence condition: v ≡ 3 (mod 6) for v=9. -/
example : 9 % 6 = 3 := by native_decide

/-- Existence condition: v ≡ 1 (mod 6) for v=13. -/
example : 13 % 6 = 1 := by native_decide

-- ════════════════════════════════════════════════════════════════════
-- § 3. Latin squares and orthogonality (MOLS)
-- ════════════════════════════════════════════════════════════════════

/-- For prime p, MOLS(p) = p - 1. MOLS(3) = 2. -/
example : 3 - 1 = 2 := by native_decide

/-- MOLS(5) = 4. -/
example : 5 - 1 = 4 := by native_decide

/-- MOLS(7) = 6. -/
example : 7 - 1 = 6 := by native_decide

/-- MOLS(11) = 10. -/
example : 11 - 1 = 10 := by native_decide

-- ════════════════════════════════════════════════════════════════════
-- § 4. Hadamard matrices
-- ════════════════════════════════════════════════════════════════════

/-- Hadamard determinant bound: |det(H_4)| = 4^(4/2) = 16. -/
example : 4 ^ 2 = 16 := by native_decide

/-- |det(H_8)| = 8^4 = 4096. -/
example : 8 ^ 4 = 4096 := by native_decide

/-- |det(H_12)| = 12^6 = 2985984. -/
example : 12 ^ 6 = 2985984 := by native_decide

/-- Order 4 is divisible by 4. -/
example : 4 % 4 = 0 := by native_decide

/-- Order 8 is divisible by 4. -/
example : 8 % 4 = 0 := by native_decide

/-- Order 12 is divisible by 4. -/
example : 12 % 4 = 0 := by native_decide

/-- Order 20 is divisible by 4. -/
example : 20 % 4 = 0 := by native_decide

-- ════════════════════════════════════════════════════════════════════
-- § 5. Projective planes
-- ════════════════════════════════════════════════════════════════════

/-- Projective plane of order 2 (Fano): n²+n+1 = 7 points. -/
example : 2 ^ 2 + 2 + 1 = 7 := by native_decide

/-- Order 3: 13 points. -/
example : 3 ^ 2 + 3 + 1 = 13 := by native_decide

/-- Order 4: 21 points. -/
example : 4 ^ 2 + 4 + 1 = 21 := by native_decide

/-- Order 7: 57 points. -/
example : 7 ^ 2 + 7 + 1 = 57 := by native_decide

/-- Order 8: 73 points. -/
example : 8 ^ 2 + 8 + 1 = 73 := by native_decide

-- ════════════════════════════════════════════════════════════════════
-- § 6. Ramsey numbers (small known values)
-- ════════════════════════════════════════════════════════════════════

/-- Known small Ramsey numbers: R(3,3)=6, R(3,4)=9, R(3,5)=14,
    R(4,4)=18, R(3,6)=18, R(3,7)=23. -/
def ramseyTable : Fin 6 → ℕ := ![6, 9, 14, 18, 18, 23]

/-- Ramsey upper bound R(s,t) ≤ C(s+t-2, s-1). R(3,3) ≤ C(4,2) = 6. -/
example : Nat.choose 4 2 = 6 := by native_decide

/-- R(3,4) = 9 ≤ C(5,2) = 10. -/
example : 9 ≤ Nat.choose 5 2 := by native_decide

/-- R(4,4) = 18 ≤ C(6,3) = 20. -/
example : 18 ≤ Nat.choose 6 3 := by native_decide

/-- Block count of a `2-(v,k,lambda)` design after integer division. -/
def bibdBlockCount (v k lambda : ℕ) : ℕ :=
  lambda * v * (v - 1) / (k * (k - 1))

theorem bibdBlockCount_fano :
    bibdBlockCount 7 3 1 = 7 := by
  native_decide

/-- Projective-plane point count for order `q`. -/
def projectivePlanePointCount (q : ℕ) : ℕ :=
  q ^ 2 + q + 1

theorem projectivePlanePointCount_four :
    projectivePlanePointCount 4 = 21 := by
  native_decide



structure DesignTheoryBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DesignTheoryBudgetCertificate.controlled
    (c : DesignTheoryBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def DesignTheoryBudgetCertificate.budgetControlled
    (c : DesignTheoryBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def DesignTheoryBudgetCertificate.Ready
    (c : DesignTheoryBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def DesignTheoryBudgetCertificate.size
    (c : DesignTheoryBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem designTheory_budgetCertificate_le_size
    (c : DesignTheoryBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleDesignTheoryBudgetCertificate :
    DesignTheoryBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleDesignTheoryBudgetCertificate.Ready := by
  constructor
  · norm_num [DesignTheoryBudgetCertificate.controlled,
      sampleDesignTheoryBudgetCertificate]
  · norm_num [DesignTheoryBudgetCertificate.budgetControlled,
      sampleDesignTheoryBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleDesignTheoryBudgetCertificate.certificateBudgetWindow ≤
      sampleDesignTheoryBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleDesignTheoryBudgetCertificate.Ready := by
  constructor
  · norm_num [DesignTheoryBudgetCertificate.controlled,
      sampleDesignTheoryBudgetCertificate]
  · norm_num [DesignTheoryBudgetCertificate.budgetControlled,
      sampleDesignTheoryBudgetCertificate]

example :
    sampleDesignTheoryBudgetCertificate.certificateBudgetWindow ≤
      sampleDesignTheoryBudgetCertificate.size := by
  apply designTheory_budgetCertificate_le_size
  constructor
  · norm_num [DesignTheoryBudgetCertificate.controlled,
      sampleDesignTheoryBudgetCertificate]
  · norm_num [DesignTheoryBudgetCertificate.budgetControlled,
      sampleDesignTheoryBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List DesignTheoryBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleDesignTheoryBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleDesignTheoryBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch2.DesignTheory
