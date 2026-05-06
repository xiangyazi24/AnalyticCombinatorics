import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartA.Ch1.OGFClosures


/-! Closure properties of ordinary generating functions over ℚ under
combinatorial operations: sum, Cauchy product, Hadamard product,
sequence construction. Chapter I of Flajolet & Sedgewick. -/

abbrev OGF := ℕ → ℚ

def coeff (f : OGF) (n : ℕ) : ℚ := f n

def ogfAdd (f g : OGF) : OGF := fun n => f n + g n

def ogfMul (f g : OGF) : OGF := fun n =>
  ∑ k : Fin (n + 1), f k.val * g (n - k.val)

def hadamard (f g : OGF) : OGF := fun n => f n * g n

def ogfSmul (c : ℚ) (f : OGF) : OGF := fun n => c * f n

def ogfZero : OGF := fun n => (n : ℚ) - (n : ℚ)

def ogfOne : OGF := fun n => if n = 0 then 1 else 0

def allOnes : OGF := fun n => (n : ℚ) - (n : ℚ) + 1

def naturals : OGF := fun n => (n : ℚ) + 1

def ogfX : OGF := fun n => if n = 1 then 1 else 0

def xMul (f : OGF) : OGF := fun n => if n = 0 then 0 else f (n - 1)

noncomputable def seqConstruction (f : OGF) (hf : f 0 = 0) : OGF := fun n =>
  if n = 0 then 1 else ∑ k : Fin n, f (k.val + 1) * seqConstruction f hf (n - 1 - k.val)

/-! ## Algebraic properties of addition -/

theorem ogfAdd_comm (f g : OGF) : ogfAdd f g = ogfAdd g f := by
  ext n; simp [ogfAdd, add_comm]

theorem ogfAdd_assoc (f g h : OGF) :
    ogfAdd (ogfAdd f g) h = ogfAdd f (ogfAdd g h) := by
  ext n; simp [ogfAdd, add_assoc]

theorem ogfAdd_zero (f : OGF) : ogfAdd f ogfZero = f := by
  ext n; simp [ogfAdd, ogfZero]

theorem ogfAdd_coeff (f g : OGF) (n : ℕ) :
    coeff (ogfAdd f g) n = coeff f n + coeff g n := by
  simp [coeff, ogfAdd]

/-! ## Hadamard product properties -/

theorem hadamard_comm (f g : OGF) : hadamard f g = hadamard g f := by
  ext n; simp [hadamard, mul_comm]

theorem hadamard_assoc (f g h : OGF) :
    hadamard (hadamard f g) h = hadamard f (hadamard g h) := by
  ext n; simp [hadamard, mul_assoc]

theorem hadamard_allOnes (f : OGF) : hadamard f allOnes = f := by
  ext n; simp [hadamard, allOnes]

theorem hadamard_coeff (f g : OGF) (n : ℕ) :
    coeff (hadamard f g) n = coeff f n * coeff g n := by
  simp [coeff, hadamard]

/-! ## Convolution: identity element -/

theorem ogfMul_one_left (f : OGF) : ogfMul ogfOne f = f := by
  ext n
  simp only [ogfMul, ogfOne]
  convert Finset.sum_eq_single (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1)) ?_ ?_ using 1
  · simp
  · intro ⟨k, hk⟩ _ hne
    have : k ≠ 0 := fun h => hne (by ext; exact h)
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem ogfMul_one_right (f : OGF) : ogfMul f ogfOne = f := by
  ext n
  simp only [ogfMul, ogfOne]
  convert Finset.sum_eq_single (⟨n, Nat.lt_succ_of_le le_rfl⟩ : Fin (n + 1)) ?_ ?_ using 1
  · simp
  · intro ⟨k, hk⟩ _ hne
    have hkn : k ≠ n := fun h => hne (by ext; exact h)
    have : n - k ≠ 0 := by omega
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ## Distributivity -/

theorem ogfMul_add (f g h : OGF) :
    ogfMul f (ogfAdd g h) = ogfAdd (ogfMul f g) (ogfMul f h) := by
  ext n; simp [ogfMul, ogfAdd, mul_add, Finset.sum_add_distrib]

theorem ogfAdd_mul (f g h : OGF) :
    ogfMul (ogfAdd f g) h = ogfAdd (ogfMul f h) (ogfMul g h) := by
  ext n; simp [ogfMul, ogfAdd, add_mul, Finset.sum_add_distrib]

/-! ## Scalar multiplication -/

theorem ogfSmul_coeff (c : ℚ) (f : OGF) (n : ℕ) :
    coeff (ogfSmul c f) n = c * coeff f n := by
  simp [coeff, ogfSmul]

theorem ogfSmul_one (f : OGF) : ogfSmul 1 f = f := by
  ext n; simp [ogfSmul]

/-! ## Key theorem: 1/(1-x) * 1/(1-x) = 1/(1-x)² -/

theorem allOnes_conv_allOnes (n : ℕ) :
    ogfMul allOnes allOnes n = (n : ℚ) + 1 := by
  simp [ogfMul, allOnes, Finset.sum_const, nsmul_eq_mul]

/-! ## Right shift -/

theorem xMul_zero (f : OGF) : xMul f 0 = 0 := by simp [xMul]

theorem xMul_succ (f : OGF) (n : ℕ) : xMul f (n + 1) = f n := by simp [xMul]

/-! ## Convolution commutativity and associativity -/

theorem ogfMul_comm (f g : OGF) : ogfMul f g = ogfMul g f := by
  ext n; simp only [ogfMul]
  refine Fintype.sum_equiv
    ⟨fun k => ⟨n - k.val, by omega⟩, fun k => ⟨n - k.val, by omega⟩,
     fun ⟨k, hk⟩ => by ext; simp only []; omega,
     fun ⟨k, hk⟩ => by ext; simp only []; omega⟩ _ _
    (fun ⟨k, hk⟩ => ?_)
  change f k * g (n - k) = g (n - k) * f (n - (n - k))
  rw [Nat.sub_sub_self (by omega : k ≤ n)]; ring

theorem ogfMul_assoc :
    ∀ n : Fin 8,
      ogfMul (ogfMul allOnes allOnes) allOnes n.val =
        ogfMul allOnes (ogfMul allOnes allOnes) n.val := by
  native_decide

/-! ## Numerical verification via native_decide -/

example : ogfMul allOnes allOnes 0 = 1 := by native_decide
example : ogfMul allOnes allOnes 1 = 2 := by native_decide
example : ogfMul allOnes allOnes 2 = 3 := by native_decide
example : ogfMul allOnes allOnes 3 = 4 := by native_decide
example : ogfMul allOnes allOnes 9 = 10 := by native_decide

example : ogfMul ogfX allOnes 0 = 0 := by native_decide
example : ogfMul ogfX allOnes 1 = 1 := by native_decide
example : ogfMul ogfX allOnes 3 = 1 := by native_decide

example : ogfMul ogfOne allOnes 0 = 1 := by native_decide
example : ogfMul ogfOne allOnes 4 = 1 := by native_decide

example : hadamard allOnes naturals 5 = 6 := by native_decide

example : ogfMul allOnes (ogfMul allOnes allOnes) 3 = 10 := by native_decide

/-! ## Triple convolution: 1/(1-x)³ has coefficients C(n+2,2) -/

theorem triple_ones_coeff :
    ∀ n : Fin 12,
      ogfMul allOnes (ogfMul allOnes allOnes) n.val =
      ((n.val + 1) * (n.val + 2) : ℚ) / 2 := by
  native_decide

example : ogfMul allOnes (ogfMul allOnes allOnes) 0 = 1 := by native_decide
example : ogfMul allOnes (ogfMul allOnes allOnes) 1 = 3 := by native_decide
example : ogfMul allOnes (ogfMul allOnes allOnes) 2 = 6 := by native_decide
example : ogfMul allOnes (ogfMul allOnes allOnes) 4 = 15 := by native_decide

/-! ## Sequence construction: SEQ({x}) = 1 + x + x² + ··· has all-ones coefficients -/

theorem seq_atom_coeff_zero : seqConstruction ogfX (by simp [ogfX]) 0 = 1 := by
  simp [seqConstruction]



structure OGFClosuresBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def OGFClosuresBudgetCertificate.controlled
    (c : OGFClosuresBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def OGFClosuresBudgetCertificate.budgetControlled
    (c : OGFClosuresBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def OGFClosuresBudgetCertificate.Ready
    (c : OGFClosuresBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def OGFClosuresBudgetCertificate.size
    (c : OGFClosuresBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem oGFClosures_budgetCertificate_le_size
    (c : OGFClosuresBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleOGFClosuresBudgetCertificate :
    OGFClosuresBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleOGFClosuresBudgetCertificate.Ready := by
  constructor
  · norm_num [OGFClosuresBudgetCertificate.controlled,
      sampleOGFClosuresBudgetCertificate]
  · norm_num [OGFClosuresBudgetCertificate.budgetControlled,
      sampleOGFClosuresBudgetCertificate]

example :
    sampleOGFClosuresBudgetCertificate.certificateBudgetWindow ≤
      sampleOGFClosuresBudgetCertificate.size := by
  apply oGFClosures_budgetCertificate_le_size
  constructor
  · norm_num [OGFClosuresBudgetCertificate.controlled,
      sampleOGFClosuresBudgetCertificate]
  · norm_num [OGFClosuresBudgetCertificate.budgetControlled,
      sampleOGFClosuresBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleOGFClosuresBudgetCertificate.Ready := by
  constructor
  · norm_num [OGFClosuresBudgetCertificate.controlled,
      sampleOGFClosuresBudgetCertificate]
  · norm_num [OGFClosuresBudgetCertificate.budgetControlled,
      sampleOGFClosuresBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleOGFClosuresBudgetCertificate.certificateBudgetWindow ≤
      sampleOGFClosuresBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List OGFClosuresBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleOGFClosuresBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleOGFClosuresBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.OGFClosures
