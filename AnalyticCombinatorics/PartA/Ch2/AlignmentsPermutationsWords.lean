import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Alignments, permutations, and words.

Finite windows for labelled arrangements, cycle decompositions, and word
assignments.
-/

namespace AnalyticCombinatorics.PartA.Ch2.AlignmentsPermutationsWords

/-- Arrangement count model: injective words of length `k` over `n` labels. -/
def fallingFactorial : ℕ → ℕ → ℕ
  | _n, 0 => 1
  | 0, _k + 1 => 0
  | n + 1, k + 1 => (n + 1) * fallingFactorial n k

/-- Finite audit that arrangements are bounded by all words. -/
def arrangementWordEnvelopeCheck (n N : ℕ) : Bool :=
  (List.range (N + 1)).all fun k => fallingFactorial n k ≤ n ^ k

theorem fallingFactorial_samples :
    fallingFactorial 4 0 = 1 ∧
    fallingFactorial 4 1 = 4 ∧
    fallingFactorial 4 2 = 12 := by
  native_decide

theorem arrangementWordEnvelope_window :
    arrangementWordEnvelopeCheck 4 4 = true := by
  unfold arrangementWordEnvelopeCheck fallingFactorial
  native_decide

structure AlignmentPermutationWordData where
  labelCount : ℕ
  blockCount : ℕ
  wordAlphabet : ℕ
  arrangementWindow : ℕ
  alignmentSlack : ℕ
deriving DecidableEq, Repr

def alignmentPermutationWordReady
    (d : AlignmentPermutationWordData) : Prop :=
  0 < d.labelCount ∧ 0 < d.wordAlphabet ∧
    d.arrangementWindow ≤ d.labelCount * d.wordAlphabet + d.blockCount + d.alignmentSlack

def alignmentPermutationWordBudget
    (d : AlignmentPermutationWordData) : ℕ :=
  d.labelCount + d.blockCount + d.wordAlphabet + d.arrangementWindow + d.alignmentSlack

theorem arrangementWindow_le_budget
    (d : AlignmentPermutationWordData) :
    d.arrangementWindow ≤
      alignmentPermutationWordBudget d + d.labelCount * d.wordAlphabet := by
  unfold alignmentPermutationWordBudget
  omega

def sampleAlignmentPermutationWordData : AlignmentPermutationWordData :=
  { labelCount := 4
    blockCount := 3
    wordAlphabet := 2
    arrangementWindow := 10
    alignmentSlack := 1 }

example : alignmentPermutationWordReady sampleAlignmentPermutationWordData := by
  norm_num [alignmentPermutationWordReady, sampleAlignmentPermutationWordData]

structure AlignmentsPermutationsWordsBudgetCertificate where
  labelWindow : ℕ
  alphabetWindow : ℕ
  blockWindow : ℕ
  arrangementWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AlignmentsPermutationsWordsBudgetCertificate.controlled
    (c : AlignmentsPermutationsWordsBudgetCertificate) : Prop :=
  0 < c.labelWindow ∧ 0 < c.alphabetWindow ∧
    c.arrangementWindow ≤ c.labelWindow * c.alphabetWindow + c.blockWindow + c.slack

def AlignmentsPermutationsWordsBudgetCertificate.budgetControlled
    (c : AlignmentsPermutationsWordsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.labelWindow + c.alphabetWindow + c.blockWindow + c.arrangementWindow + c.slack

def AlignmentsPermutationsWordsBudgetCertificate.Ready
    (c : AlignmentsPermutationsWordsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AlignmentsPermutationsWordsBudgetCertificate.size
    (c : AlignmentsPermutationsWordsBudgetCertificate) : ℕ :=
  c.labelWindow + c.alphabetWindow + c.blockWindow + c.arrangementWindow + c.slack

theorem alignmentsPermutationsWords_budgetCertificate_le_size
    (c : AlignmentsPermutationsWordsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleAlignmentsPermutationsWordsBudgetCertificate :
    AlignmentsPermutationsWordsBudgetCertificate :=
  { labelWindow := 4
    alphabetWindow := 2
    blockWindow := 3
    arrangementWindow := 10
    certificateBudgetWindow := 20
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAlignmentsPermutationsWordsBudgetCertificate.Ready := by
  constructor
  · norm_num [AlignmentsPermutationsWordsBudgetCertificate.controlled,
      sampleAlignmentsPermutationsWordsBudgetCertificate]
  · norm_num [AlignmentsPermutationsWordsBudgetCertificate.budgetControlled,
      sampleAlignmentsPermutationsWordsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAlignmentsPermutationsWordsBudgetCertificate.certificateBudgetWindow ≤
      sampleAlignmentsPermutationsWordsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAlignmentsPermutationsWordsBudgetCertificate.Ready := by
  constructor
  · norm_num [AlignmentsPermutationsWordsBudgetCertificate.controlled,
      sampleAlignmentsPermutationsWordsBudgetCertificate]
  · norm_num [AlignmentsPermutationsWordsBudgetCertificate.budgetControlled,
      sampleAlignmentsPermutationsWordsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List AlignmentsPermutationsWordsBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleAlignmentsPermutationsWordsBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleAlignmentsPermutationsWordsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch2.AlignmentsPermutationsWords
