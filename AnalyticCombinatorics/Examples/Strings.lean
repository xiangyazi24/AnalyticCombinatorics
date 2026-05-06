import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Binary string examples.

Binary strings of length `n` are counted by `2^n`.
-/

namespace AnalyticCombinatorics.Examples.Strings

def binaryStringCount (n : ℕ) : ℕ := 2 ^ n

def alphabetStringCount (alphabetSize wordLength : ℕ) : ℕ :=
  alphabetSize ^ wordLength

def binaryWords : ℕ → Finset (List (Fin 2))
  | 0 => {[]}
  | n + 1 =>
      (Finset.univ.product (binaryWords n)).image fun pair => pair.1 :: pair.2

theorem mem_binaryWords_length {xs : List (Fin 2)} {n : ℕ} :
    xs ∈ binaryWords n ↔ xs.length = n := by
  revert xs
  induction n with
  | zero =>
      intro xs
      cases xs <;> simp [binaryWords]
  | succ n ih =>
      intro xs
      cases xs with
      | nil =>
          simp [binaryWords]
      | cons b xs =>
          simp [binaryWords, ih]

def binaryWordsByEnumeration (n : ℕ) : ℕ :=
  (binaryWords n).card

structure StringExampleWindow where
  alphabetSize : ℕ
  wordLength : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def stringExampleReady (w : StringExampleWindow) : Prop :=
  0 < w.alphabetSize ∧ w.wordLength ≤ w.alphabetSize + w.slack

def stringExampleBudget (w : StringExampleWindow) : ℕ :=
  w.alphabetSize + w.wordLength + w.slack

theorem stringExampleReady.certificate {w : StringExampleWindow}
    (h : stringExampleReady w) :
    0 < w.alphabetSize ∧ w.wordLength ≤ w.alphabetSize + w.slack ∧
      w.wordLength ≤ stringExampleBudget w := by
  rcases h with ⟨halphabet, hlength⟩
  refine ⟨halphabet, hlength, ?_⟩
  unfold stringExampleBudget
  omega

def sampleStringExampleWindow : StringExampleWindow :=
  { alphabetSize := 2, wordLength := 5, slack := 3 }

example : stringExampleReady sampleStringExampleWindow := by
  norm_num [stringExampleReady, sampleStringExampleWindow]

example : binaryStringCount 0 = 1 := by native_decide
example : binaryStringCount 1 = 2 := by native_decide
example : binaryStringCount 2 = 4 := by native_decide
example : binaryStringCount 3 = 8 := by native_decide
example : binaryStringCount 4 = 16 := by native_decide
example : binaryStringCount 5 = 32 := by native_decide
example : binaryStringCount 10 = 1024 := by native_decide
example : alphabetStringCount 3 4 = 81 := by native_decide
example : binaryWordsByEnumeration 4 = binaryStringCount 4 := by native_decide
example : stringExampleBudget sampleStringExampleWindow = 10 := by native_decide

theorem binaryStringCount_values_0_to_10 :
    (List.range 11).map binaryStringCount =
      [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024] := by
  native_decide

structure StringsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def StringsBudgetCertificate.controlled
    (c : StringsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def StringsBudgetCertificate.budgetControlled
    (c : StringsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def StringsBudgetCertificate.Ready (c : StringsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def StringsBudgetCertificate.size (c : StringsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem strings_budgetCertificate_le_size
    (c : StringsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleStringsBudgetCertificate : StringsBudgetCertificate :=
  { primaryWindow := 4
    secondaryWindow := 5
    certificateBudgetWindow := 10
    slack := 1 }

example : sampleStringsBudgetCertificate.Ready := by
  constructor
  · norm_num [StringsBudgetCertificate.controlled,
      sampleStringsBudgetCertificate]
  · norm_num [StringsBudgetCertificate.budgetControlled,
      sampleStringsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleStringsBudgetCertificate.Ready := by
  constructor
  · norm_num [StringsBudgetCertificate.controlled,
      sampleStringsBudgetCertificate]
  · norm_num [StringsBudgetCertificate.budgetControlled,
      sampleStringsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleStringsBudgetCertificate.certificateBudgetWindow ≤
      sampleStringsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List StringsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleStringsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleStringsBudgetCertificate
  native_decide

end AnalyticCombinatorics.Examples.Strings
