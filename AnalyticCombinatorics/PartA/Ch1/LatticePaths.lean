import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Lattice path count checks.

This file keeps a finite, computable model of rectangular paths and Dyck
paths.  It avoids cross-file dependencies so the chapter slice remains
independent under the repository-wide `Mathlib.Tactic` import policy.
-/

namespace AnalyticCombinatorics.PartA.Ch1.LatticePaths

/-! ## Rectangular lattice paths -/

def rectanglePathCount (east north : ℕ) : ℕ :=
  Nat.choose (east + north) east

def centralBinomial (n : ℕ) : ℕ :=
  rectanglePathCount n n

def pathWindowBudget (east north slack : ℕ) : ℕ :=
  east + north + slack

structure PathWindow where
  east : ℕ
  north : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def hasEndpoint (w : PathWindow) : Prop :=
  0 < w.east + w.north

def northControlled (w : PathWindow) : Prop :=
  w.north ≤ w.east + w.slack

def pathWindowReady (w : PathWindow) : Prop :=
  hasEndpoint w ∧ northControlled w

def pathWindowSize (w : PathWindow) : ℕ :=
  pathWindowBudget w.east w.north w.slack

theorem pathWindowReady.certificate {w : PathWindow}
    (h : pathWindowReady w) :
    hasEndpoint w ∧ northControlled w ∧ w.north ≤ pathWindowSize w := by
  rcases h with ⟨hend, hcontrolled⟩
  refine ⟨hend, hcontrolled, ?_⟩
  unfold pathWindowSize pathWindowBudget
  omega

theorem east_le_pathWindowSize (w : PathWindow) :
    w.east ≤ pathWindowSize w := by
  unfold pathWindowSize pathWindowBudget
  omega

/-! ## Dyck paths -/

inductive Step where
  | up
  | down
deriving DecidableEq, Repr

namespace Step

def words : ℕ → Finset (List Step)
  | 0 => {[]}
  | n + 1 =>
      (words n).image (fun xs => Step.up :: xs) ∪
        (words n).image (fun xs => Step.down :: xs)

theorem mem_words_iff {xs : List Step} {n : ℕ} :
    xs ∈ words n ↔ xs.length = n := by
  revert xs
  induction n with
  | zero =>
      intro xs
      cases xs <;> simp [words]
  | succ n ih =>
      intro xs
      cases xs with
      | nil =>
          simp [words]
      | cons s xs =>
          cases s <;> simp [words, ih]

end Step

def finalHeightFrom : ℕ → List Step → ℕ
  | h, [] => h
  | h, Step.up :: xs => finalHeightFrom (h + 1) xs
  | h, Step.down :: xs => finalHeightFrom (h - 1) xs

def prefixesNonnegativeFrom : ℕ → List Step → Bool
  | _, [] => true
  | h, Step.up :: xs => prefixesNonnegativeFrom (h + 1) xs
  | 0, Step.down :: _ => false
  | h + 1, Step.down :: xs => prefixesNonnegativeFrom h xs

def isDyckWord (xs : List Step) : Prop :=
  prefixesNonnegativeFrom 0 xs = true ∧ finalHeightFrom 0 xs = 0

instance (xs : List Step) : Decidable (isDyckWord xs) := by
  unfold isDyckWord
  infer_instance

def dyckWords (n : ℕ) : Finset (List Step) :=
  (Step.words (2 * n)).filter isDyckWord

def dyckPathCount (n : ℕ) : ℕ :=
  (dyckWords n).card

def catalanNumber (n : ℕ) : ℕ :=
  Nat.choose (2 * n) n / (n + 1)

theorem mem_dyckWords_length {xs : List Step} {n : ℕ}
    (h : xs ∈ dyckWords n) :
    xs.length = 2 * n := by
  have hword : xs ∈ Step.words (2 * n) := (Finset.mem_filter.mp h).1
  exact Step.mem_words_iff.mp hword

theorem dyckWords_subset_words (n : ℕ) :
    dyckWords n ⊆ Step.words (2 * n) := by
  intro xs hxs
  exact (Finset.mem_filter.mp hxs).1

def binaryTreeCatalanTable : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 5
  | 4 => 14
  | 5 => 42
  | _ => 0

def samplePathWindow : PathWindow :=
  { east := 4, north := 3, slack := 1 }

example : pathWindowReady samplePathWindow := by
  norm_num [pathWindowReady, hasEndpoint]
  norm_num [northControlled, samplePathWindow]

example : centralBinomial 0 = 1 := by native_decide
example : centralBinomial 3 = 20 := by native_decide
example : centralBinomial 5 = 252 := by native_decide
example : rectanglePathCount 2 3 = 10 := by native_decide
example : pathWindowSize samplePathWindow = 8 := by native_decide
example : dyckPathCount 0 = 1 := by native_decide
example : dyckPathCount 1 = 1 := by native_decide
example : dyckPathCount 2 = 2 := by native_decide
example : dyckPathCount 3 = 5 := by native_decide
example : dyckPathCount 4 = 14 := by native_decide
example : catalanNumber 4 = dyckPathCount 4 := by native_decide
example : binaryTreeCatalanTable 5 = 42 := by native_decide


structure LatticePathsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LatticePathsBudgetCertificate.controlled
    (c : LatticePathsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def LatticePathsBudgetCertificate.budgetControlled
    (c : LatticePathsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def LatticePathsBudgetCertificate.Ready
    (c : LatticePathsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LatticePathsBudgetCertificate.size
    (c : LatticePathsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem latticePaths_budgetCertificate_le_size
    (c : LatticePathsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleLatticePathsBudgetCertificate :
    LatticePathsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleLatticePathsBudgetCertificate.Ready := by
  constructor
  · norm_num [LatticePathsBudgetCertificate.controlled,
      sampleLatticePathsBudgetCertificate]
  · norm_num [LatticePathsBudgetCertificate.budgetControlled,
      sampleLatticePathsBudgetCertificate]

example :
    sampleLatticePathsBudgetCertificate.certificateBudgetWindow ≤
      sampleLatticePathsBudgetCertificate.size := by
  apply latticePaths_budgetCertificate_le_size
  constructor
  · norm_num [LatticePathsBudgetCertificate.controlled,
      sampleLatticePathsBudgetCertificate]
  · norm_num [LatticePathsBudgetCertificate.budgetControlled,
      sampleLatticePathsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleLatticePathsBudgetCertificate.Ready := by
  constructor
  · norm_num [LatticePathsBudgetCertificate.controlled,
      sampleLatticePathsBudgetCertificate]
  · norm_num [LatticePathsBudgetCertificate.budgetControlled,
      sampleLatticePathsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleLatticePathsBudgetCertificate.certificateBudgetWindow ≤
      sampleLatticePathsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List LatticePathsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleLatticePathsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleLatticePathsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.LatticePaths
