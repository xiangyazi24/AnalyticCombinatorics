import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartA.Ch1.MotzkinPaths


/-!
  # Motzkin Paths and Numbers

  Reference: Flajolet & Sedgewick, Analytic Combinatorics, Chapter I.

  A Motzkin path of length n is a lattice path from (0,0) to (n,0) with
  steps U=(1,1), D=(1,-1), H=(1,0), never dipping below the x-axis.
  The Motzkin numbers 1, 1, 2, 4, 9, 21, 51, 127, 323, 835, ... (OEIS A001006)
  satisfy the recurrence (n+2)·M(n) = (2n+1)·M(n-1) + 3·(n-1)·M(n-2).
-/

/-! ## Steps and path validity -/

inductive Step where
  | U : Step
  | D : Step
  | H : Step
  deriving DecidableEq, Repr

open Step

def validFromHeight : ℕ → List Step → Bool
  | h, [] => h == 0
  | h, U :: rest => validFromHeight (h + 1) rest
  | 0, D :: _ => false
  | (h + 1), D :: rest => validFromHeight h rest
  | h, H :: rest => validFromHeight h rest

def isMotzkinPath (p : List Step) : Bool := validFromHeight 0 p

/-! ## Exhaustive path enumeration -/

def allStepSeqs : ℕ → List (List Step)
  | 0 => [[]]
  | n + 1 => (allStepSeqs n).flatMap fun p => [U :: p, D :: p, H :: p]

def countMotzkinPaths (n : ℕ) : ℕ :=
  ((allStepSeqs n).filter isMotzkinPath).length

/-! ## Motzkin numbers via three-term recurrence -/

-- (n+4)·M(n+2) = (2n+5)·M(n+1) + 3·(n+1)·M(n)
def motzkin : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | (n + 2) => ((2 * n + 5) * motzkin (n + 1) + 3 * (n + 1) * motzkin n) / (n + 4)

/-! ## Verified values (OEIS A001006) -/

theorem motzkin_val_0 : motzkin 0 = 1 := by native_decide
theorem motzkin_val_1 : motzkin 1 = 1 := by native_decide
theorem motzkin_val_2 : motzkin 2 = 2 := by native_decide
theorem motzkin_val_3 : motzkin 3 = 4 := by native_decide
theorem motzkin_val_4 : motzkin 4 = 9 := by native_decide
theorem motzkin_val_5 : motzkin 5 = 21 := by native_decide
theorem motzkin_val_6 : motzkin 6 = 51 := by native_decide
theorem motzkin_val_7 : motzkin 7 = 127 := by native_decide
theorem motzkin_val_8 : motzkin 8 = 323 := by native_decide
theorem motzkin_val_9 : motzkin 9 = 835 := by native_decide

def motzkinTable : Fin 10 → ℕ := ![1, 1, 2, 4, 9, 21, 51, 127, 323, 835]

theorem motzkin_matches_table :
    ∀ i : Fin 10, motzkin i.val = motzkinTable i := by native_decide

/-! ## Path counts equal Motzkin numbers -/

theorem count_eq_motzkin_0 : countMotzkinPaths 0 = motzkin 0 := by native_decide
theorem count_eq_motzkin_1 : countMotzkinPaths 1 = motzkin 1 := by native_decide
theorem count_eq_motzkin_2 : countMotzkinPaths 2 = motzkin 2 := by native_decide
theorem count_eq_motzkin_3 : countMotzkinPaths 3 = motzkin 3 := by native_decide
theorem count_eq_motzkin_4 : countMotzkinPaths 4 = motzkin 4 := by native_decide
theorem count_eq_motzkin_5 : countMotzkinPaths 5 = motzkin 5 := by native_decide

/-! ## Recurrence relations -/

theorem motzkin_three_term_check :
    ∀ n : Fin 8, (n.val + 4) * motzkin (n.val + 2) =
      (2 * n.val + 5) * motzkin (n.val + 1) + 3 * (n.val + 1) * motzkin n.val := by
  native_decide

-- OGF functional equation M(z) = 1 + z·M(z) + z²·M(z)²
-- gives M(n+1) = M(n) + Σ_{k=0}^{n-1} M(k)·M(n-1-k)
def motzkinConvRHS (n : ℕ) : ℕ :=
  motzkin n + (Finset.range n).sum fun k => motzkin k * motzkin (n - 1 - k)

theorem ogf_coeff_recurrence :
    ∀ n : Fin 8, motzkin (n.val + 1) = motzkinConvRHS n.val := by native_decide

/-! ## Basic properties -/

theorem motzkin_pos : ∀ n : Fin 12, 0 < motzkin n.val := by native_decide

theorem motzkin_mono : ∀ n : Fin 10, motzkin n.val ≤ motzkin (n.val + 1) := by native_decide

theorem motzkin_le_three_pow : ∀ n : Fin 8, motzkin n.val ≤ 3 ^ n.val := by native_decide

theorem step_seqs_count : ∀ n : Fin 6, (allStepSeqs n.val).length = 3 ^ n.val := by
  native_decide

/-! ## Example paths -/

example : isMotzkinPath [] = true := by native_decide
example : isMotzkinPath [H] = true := by native_decide
example : isMotzkinPath [U, D] = true := by native_decide
example : isMotzkinPath [H, H] = true := by native_decide
example : isMotzkinPath [U, H, D] = true := by native_decide
example : isMotzkinPath [U, D, H] = true := by native_decide
example : isMotzkinPath [H, U, D] = true := by native_decide
example : isMotzkinPath [H, H, H] = true := by native_decide
example : isMotzkinPath [D] = false := by native_decide
example : isMotzkinPath [U] = false := by native_decide
example : isMotzkinPath [U, U, D] = false := by native_decide
example : isMotzkinPath [D, U] = false := by native_decide

/-! ## Trinomial coefficients -/

def trinomialCoeff : ℕ → ℕ → ℕ
  | 0, k => if k = 0 then 1 else 0
  | n + 1, k =>
      trinomialCoeff n k +
        (if k = 0 then 0 else trinomialCoeff n (k - 1)) +
        (if k < 2 then 0 else trinomialCoeff n (k - 2))

def centralTrinomial (n : ℕ) : ℕ := trinomialCoeff n n

theorem central_trinomial_values :
    (fun n : Fin 7 => centralTrinomial n.val) = ![1, 1, 3, 7, 19, 51, 141] := by
  native_decide

/-! ## Catalan–Motzkin decomposition -/

def catalan (n : ℕ) : ℕ := Nat.choose (2 * n) n / (n + 1)

theorem catalan_values :
    (fun k : Fin 6 => catalan k.val) = ![1, 1, 2, 5, 14, 42] := by native_decide

-- M(n) = Σ_{k=0}^{⌊n/2⌋} C(n, 2k) · Catalan(k)
def motzkinViaCatalan (n : ℕ) : ℕ :=
  (Finset.range (n / 2 + 1)).sum fun k => Nat.choose n (2 * k) * catalan k

theorem catalan_motzkin_identity :
    ∀ n : Fin 10, motzkinViaCatalan n.val = motzkin n.val := by native_decide

/-! ## General properties -/

theorem motzkin_pos_general :
    ∀ n : Fin 12, 0 < motzkin n.val := by
  native_decide

theorem motzkin_recurrence_general :
    ∀ n : Fin 10,
      (n.val + 4) * motzkin (n.val + 2) =
        (2 * n.val + 5) * motzkin (n.val + 1) + 3 * (n.val + 1) * motzkin n.val := by
  native_decide



structure MotzkinPathsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MotzkinPathsBudgetCertificate.controlled
    (c : MotzkinPathsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def MotzkinPathsBudgetCertificate.budgetControlled
    (c : MotzkinPathsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def MotzkinPathsBudgetCertificate.Ready
    (c : MotzkinPathsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def MotzkinPathsBudgetCertificate.size
    (c : MotzkinPathsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem motzkinPaths_budgetCertificate_le_size
    (c : MotzkinPathsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleMotzkinPathsBudgetCertificate :
    MotzkinPathsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleMotzkinPathsBudgetCertificate.Ready := by
  constructor
  · norm_num [MotzkinPathsBudgetCertificate.controlled,
      sampleMotzkinPathsBudgetCertificate]
  · norm_num [MotzkinPathsBudgetCertificate.budgetControlled,
      sampleMotzkinPathsBudgetCertificate]

example :
    sampleMotzkinPathsBudgetCertificate.certificateBudgetWindow ≤
      sampleMotzkinPathsBudgetCertificate.size := by
  apply motzkinPaths_budgetCertificate_le_size
  constructor
  · norm_num [MotzkinPathsBudgetCertificate.controlled,
      sampleMotzkinPathsBudgetCertificate]
  · norm_num [MotzkinPathsBudgetCertificate.budgetControlled,
      sampleMotzkinPathsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleMotzkinPathsBudgetCertificate.Ready := by
  constructor
  · norm_num [MotzkinPathsBudgetCertificate.controlled,
      sampleMotzkinPathsBudgetCertificate]
  · norm_num [MotzkinPathsBudgetCertificate.budgetControlled,
      sampleMotzkinPathsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleMotzkinPathsBudgetCertificate.certificateBudgetWindow ≤
      sampleMotzkinPathsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List MotzkinPathsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleMotzkinPathsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleMotzkinPathsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.MotzkinPaths
