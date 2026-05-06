import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
String enumeration checks.

The finite models here cover ordinary strings, pointed strings, and the
standard binary language avoiding adjacent ones.
-/

namespace AnalyticCombinatorics.PartA.Ch1.StringsTheory

/-! ## Unrestricted words -/

def stringCount (alphabetSize wordLength : ℕ) : ℕ :=
  alphabetSize ^ wordLength

def pointedStringChoices (alphabetSize wordLength : ℕ) : ℕ :=
  wordLength * stringCount alphabetSize wordLength

def stringWords (alphabetSize : ℕ) : ℕ → Finset (List (Fin alphabetSize))
  | 0 => {[]}
  | n + 1 =>
      (Finset.univ.product (stringWords alphabetSize n)).image
        (fun pair => pair.1 :: pair.2)

theorem mem_stringWords_length {alphabetSize : ℕ}
    {xs : List (Fin alphabetSize)} {n : ℕ} :
    xs ∈ stringWords alphabetSize n ↔ xs.length = n := by
  revert xs
  induction n with
  | zero =>
      intro xs
      cases xs <;> simp [stringWords]
  | succ n ih =>
      intro xs
      cases xs with
      | nil =>
          simp [stringWords]
      | cons a xs =>
          simp [stringWords, ih]

def stringWordCountByEnumeration (alphabetSize wordLength : ℕ) : ℕ :=
  (stringWords alphabetSize wordLength).card

theorem stringWords_count_zero (alphabetSize : ℕ) :
    stringWordCountByEnumeration alphabetSize 0 = 1 := by
  simp [stringWordCountByEnumeration, stringWords]

/-! ## Finite windows for language restrictions -/

structure StringWindow where
  alphabetSize : ℕ
  wordLength : ℕ
  forbiddenPatterns : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def nonemptyAlphabet (w : StringWindow) : Prop :=
  0 < w.alphabetSize

def forbiddenPatternsControlled (w : StringWindow) : Prop :=
  w.forbiddenPatterns ≤ w.wordLength + w.slack

def stringWindowReady (w : StringWindow) : Prop :=
  nonemptyAlphabet w ∧ forbiddenPatternsControlled w

def stringWindowBudget (w : StringWindow) : ℕ :=
  w.alphabetSize + w.wordLength + w.forbiddenPatterns + w.slack

theorem stringWindowReady.certificate {w : StringWindow}
    (h : stringWindowReady w) :
    nonemptyAlphabet w ∧ forbiddenPatternsControlled w ∧
      w.wordLength ≤ stringWindowBudget w := by
  rcases h with ⟨halphabet, hcontrolled⟩
  refine ⟨halphabet, hcontrolled, ?_⟩
  unfold stringWindowBudget
  omega

theorem forbiddenPatterns_le_budget (w : StringWindow) :
    w.forbiddenPatterns ≤ stringWindowBudget w := by
  unfold stringWindowBudget
  omega

/-! ## Binary strings avoiding adjacent ones -/

def noConsecOnesBool : List (Fin 2) → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest =>
      if a = 1 ∧ b = 1 then
        false
      else
        noConsecOnesBool (b :: rest)

def noConsecOnes (xs : List (Fin 2)) : Prop :=
  noConsecOnesBool xs = true

instance (xs : List (Fin 2)) : Decidable (noConsecOnes xs) := by
  unfold noConsecOnes
  infer_instance

def binaryWordsAvoiding11 (n : ℕ) : Finset (List (Fin 2)) :=
  (stringWords 2 n).filter noConsecOnes

def noConsecOnesCount (n : ℕ) : ℕ :=
  (binaryWordsAvoiding11 n).card

theorem binaryWordsAvoiding11_length {xs : List (Fin 2)} {n : ℕ}
    (h : xs ∈ binaryWordsAvoiding11 n) :
    xs.length = n := by
  have hword : xs ∈ stringWords 2 n := (Finset.mem_filter.mp h).1
  exact mem_stringWords_length.mp hword

def sampleStringWindow : StringWindow :=
  { alphabetSize := 3, wordLength := 5, forbiddenPatterns := 4, slack := 1 }

example : stringWindowReady sampleStringWindow := by
  norm_num [stringWindowReady, nonemptyAlphabet]
  norm_num [forbiddenPatternsControlled, sampleStringWindow]

example : stringCount 2 10 = 1024 := by native_decide
example : stringCount 3 5 = 243 := by native_decide
example : pointedStringChoices 2 4 = 64 := by native_decide
example : stringWindowBudget sampleStringWindow = 13 := by native_decide
example : stringWordCountByEnumeration 2 4 = 16 := by native_decide
example : stringWordCountByEnumeration 3 3 = 27 := by native_decide
example : noConsecOnesCount 0 = 1 := by native_decide
example : noConsecOnesCount 1 = 2 := by native_decide
example : noConsecOnesCount 2 = 3 := by native_decide
example : noConsecOnesCount 3 = 5 := by native_decide
example : noConsecOnesCount 4 = 8 := by native_decide
example : noConsecOnesCount 5 = 13 := by native_decide


structure StringsTheoryBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def StringsTheoryBudgetCertificate.controlled
    (c : StringsTheoryBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def StringsTheoryBudgetCertificate.budgetControlled
    (c : StringsTheoryBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def StringsTheoryBudgetCertificate.Ready
    (c : StringsTheoryBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def StringsTheoryBudgetCertificate.size
    (c : StringsTheoryBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem stringsTheory_budgetCertificate_le_size
    (c : StringsTheoryBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleStringsTheoryBudgetCertificate :
    StringsTheoryBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleStringsTheoryBudgetCertificate.Ready := by
  constructor
  · norm_num [StringsTheoryBudgetCertificate.controlled,
      sampleStringsTheoryBudgetCertificate]
  · norm_num [StringsTheoryBudgetCertificate.budgetControlled,
      sampleStringsTheoryBudgetCertificate]

example :
    sampleStringsTheoryBudgetCertificate.certificateBudgetWindow ≤
      sampleStringsTheoryBudgetCertificate.size := by
  apply stringsTheory_budgetCertificate_le_size
  constructor
  · norm_num [StringsTheoryBudgetCertificate.controlled,
      sampleStringsTheoryBudgetCertificate]
  · norm_num [StringsTheoryBudgetCertificate.budgetControlled,
      sampleStringsTheoryBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleStringsTheoryBudgetCertificate.Ready := by
  constructor
  · norm_num [StringsTheoryBudgetCertificate.controlled,
      sampleStringsTheoryBudgetCertificate]
  · norm_num [StringsTheoryBudgetCertificate.budgetControlled,
      sampleStringsTheoryBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleStringsTheoryBudgetCertificate.certificateBudgetWindow ≤
      sampleStringsTheoryBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List StringsTheoryBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleStringsTheoryBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleStringsTheoryBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.StringsTheory
