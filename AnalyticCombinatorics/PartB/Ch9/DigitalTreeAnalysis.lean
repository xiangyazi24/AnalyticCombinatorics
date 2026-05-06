import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch9.DigitalTreeAnalysis


/-!
# Digital Tree Analysis

Small finite checks for the digital-tree models in Chapter IX of Flajolet and
Sedgewick: binary tries, Patricia tries, digital search trees, trie heights,
successful-search depths, and bucket overflow probabilities.  Expectations are
stored as integer numerators after a fixed scaling, so every certificate remains
decidable by computation.
-/

/-! ## Basic binary trie tables -/

/-- Number of binary strings at exact depth `d`. -/
def binaryTrieLevelSize (d : ℕ) : ℕ :=
  2 ^ d

/-- Number of binary prefixes of length at most `d`. -/
def binaryTriePrefixCapacity (d : ℕ) : ℕ :=
  2 ^ (d + 1) - 1

/-- Level sizes in the full binary trie, for `0 ≤ d ≤ 11`. -/
def binaryTrieLevelSizeTable : Fin 12 → ℕ :=
  ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

/-- Prefix capacities in the full binary trie, for `0 ≤ d ≤ 11`. -/
def binaryTriePrefixCapacityTable : Fin 12 → ℕ :=
  ![1, 3, 7, 15, 31, 63, 127, 255, 511, 1023, 2047, 4095]

theorem binaryTrieLevelSize_values :
    List.map binaryTrieLevelSize [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] =
      [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048] := by
  native_decide

theorem binaryTriePrefixCapacity_values :
    List.map binaryTriePrefixCapacity [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] =
      [1, 3, 7, 15, 31, 63, 127, 255, 511, 1023, 2047, 4095] := by
  native_decide

theorem binaryTrie_tables_match_definitions :
    List.ofFn binaryTrieLevelSizeTable =
        List.map binaryTrieLevelSize [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] ∧
      List.ofFn binaryTriePrefixCapacityTable =
        List.map binaryTriePrefixCapacity [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] := by
  native_decide

/-! ## Expected internal nodes in a truncated symmetric trie -/

/--
For `n` independent keys and a prefix of depth `d`, this is the numerator of
`P[at least two keys share the prefix]` over denominator `2^(d*n)`.
-/
def trieInternalNumerator (d n : ℕ) : ℕ :=
  if n < 2 then 0
  else 2 ^ (d * n) - (2 ^ d - 1) ^ n - n * (2 ^ d - 1) ^ (n - 1)

/--
Expected number of internal nodes in a binary trie truncated above depth `4`,
scaled by `2^(4*n)`.
-/
def scaledExpectedTrieInternalDepth4 (n : ℕ) : ℕ :=
  (Finset.range 4).sum fun d =>
    2 ^ d * (2 ^ (4 * n) / 2 ^ (d * n)) * trieInternalNumerator d n

/-- Scaled expected internal-node counts for `0 ≤ n ≤ 8`. -/
def scaledExpectedTrieInternalDepth4Table : Fin 9 → ℕ :=
  ![0, 0, 480, 12160, 265600, 5305344, 100289024, 1828603904, 32516880384]

theorem scaledExpectedTrieInternalDepth4_values :
    List.map scaledExpectedTrieInternalDepth4 [0, 1, 2, 3, 4, 5, 6, 7, 8] =
      [0, 0, 480, 12160, 265600, 5305344, 100289024, 1828603904, 32516880384] := by
  native_decide

theorem scaledExpectedTrieInternalDepth4_table_values :
    List.ofFn scaledExpectedTrieInternalDepth4Table =
      [0, 0, 480, 12160, 265600, 5305344, 100289024, 1828603904, 32516880384] := by
  native_decide

/-! ## Patricia trie size -/

/-- Patricia trie internal nodes for `n` distinct keys. -/
def patriciaInternalNodes (n : ℕ) : ℕ :=
  n - 1

/-- Patricia internal-node counts for `1 ≤ n ≤ 12`. -/
def patriciaInternalNodeTable : Fin 12 → ℕ :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

theorem patriciaInternalNode_values :
    List.map patriciaInternalNodes [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] =
      [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] := by
  native_decide

theorem patriciaInternalNode_table_values :
    List.ofFn patriciaInternalNodeTable =
      [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] := by
  native_decide

/-! ## Digital search tree comparison budgets -/

/-- Bit length of a positive natural number, with `bitLength 0 = 0`. -/
def bitLength (n : ℕ) : ℕ :=
  if n = 0 then 0 else Nat.log2 n + 1

/-- A small cumulative comparison budget for insertions into a digital search tree. -/
def dstComparisonBudget (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sum fun k => bitLength k

/-- Cumulative bit-comparison budgets for `0 ≤ n ≤ 11`. -/
def dstComparisonBudgetTable : Fin 12 → ℕ :=
  ![0, 1, 3, 5, 8, 11, 14, 17, 21, 25, 29, 33]

theorem dstComparisonBudget_values :
    List.map dstComparisonBudget [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] =
      [0, 1, 3, 5, 8, 11, 14, 17, 21, 25, 29, 33] := by
  native_decide

theorem dstComparisonBudget_table_values :
    List.ofFn dstComparisonBudgetTable =
      [0, 1, 3, 5, 8, 11, 14, 17, 21, 25, 29, 33] := by
  native_decide

/-! ## Binary trie height lower bounds -/

/-- Small lower bound `ceil(log₂ n)` for the height needed to distinguish `n` keys. -/
def binaryTrieHeightLowerBound (n : ℕ) : ℕ :=
  if n ≤ 1 then 0 else Nat.log2 (n - 1) + 1

/-- Height lower bounds for `0 ≤ n ≤ 11`. -/
def binaryTrieHeightLowerBoundTable : Fin 12 → ℕ :=
  ![0, 0, 1, 2, 2, 3, 3, 3, 3, 4, 4, 4]

/-- Boolean capacity certificate for the tabulated lower bound. -/
def binaryTrieHeightLowerBoundCert (n : ℕ) : Bool :=
  let h := binaryTrieHeightLowerBound n
  decide (n ≤ 2 ^ h ∧ (h = 0 ∨ 2 ^ (h - 1) < n))

theorem binaryTrieHeightLowerBound_values :
    List.map binaryTrieHeightLowerBound [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] =
      [0, 0, 1, 2, 2, 3, 3, 3, 3, 4, 4, 4] := by
  native_decide

theorem binaryTrieHeightLowerBound_certificates :
    List.map binaryTrieHeightLowerBoundCert [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] =
      [true, true, true, true, true, true, true, true, true, true, true, true] := by
  native_decide

/-! ## Expected depth in a symmetric full trie -/

/-- Numerator of average successful-search depth at level `d`, denominator `2^d`. -/
def symmetricTrieDepthNumerator (d : ℕ) : ℕ :=
  d * 2 ^ d

/-- Depth numerators for `0 ≤ d ≤ 11`. -/
def symmetricTrieDepthNumeratorTable : Fin 12 → ℕ :=
  ![0, 2, 8, 24, 64, 160, 384, 896, 2048, 4608, 10240, 22528]

theorem symmetricTrieDepthNumerator_values :
    List.map symmetricTrieDepthNumerator [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] =
      [0, 2, 8, 24, 64, 160, 384, 896, 2048, 4608, 10240, 22528] := by
  native_decide

theorem symmetricTrieDepthNumerator_table_values :
    List.ofFn symmetricTrieDepthNumeratorTable =
      [0, 2, 8, 24, 64, 160, 384, 896, 2048, 4608, 10240, 22528] := by
  native_decide

/-! ## Bucket trie overflow probabilities -/

/--
For one bucket among `8` equiprobable prefixes, this is the numerator of
`P[Binomial(n, 1/8) > bucket]` over denominator `8^n`.
-/
def bucketOverflowNumerator (bucket n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sum fun k =>
    if bucket < k then Nat.choose n k * 7 ^ (n - k) else 0

/-- Overflow numerators for bucket capacity `1`, `0 ≤ n ≤ 11`. -/
def bucketOverflowNumeratorCap1Table : Fin 12 → ℕ :=
  ![0, 0, 1, 22, 323, 3956, 43653, 450066, 4424071, 41980912, 387730505, 3505380110]

/-- Overflow numerators for bucket capacity `2`, `0 ≤ n ≤ 11`. -/
def bucketOverflowNumeratorCap2Table : Fin 12 → ℕ :=
  ![0, 0, 0, 1, 29, 526, 7638, 97119, 1129899, 12333364, 128314460, 1285931725]

/-- Overflow numerators for bucket capacity `3`, `0 ≤ n ≤ 11`. -/
def bucketOverflowNumeratorCap3Table : Fin 12 → ℕ :=
  ![0, 0, 0, 0, 1, 36, 778, 13084, 188707, 2450848, 29489300, 334739560]

theorem bucketOverflowNumerator_cap1_values :
    List.map (bucketOverflowNumerator 1) [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] =
      [0, 0, 1, 22, 323, 3956, 43653, 450066, 4424071, 41980912, 387730505, 3505380110] := by
  native_decide

theorem bucketOverflowNumerator_cap2_values :
    List.map (bucketOverflowNumerator 2) [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] =
      [0, 0, 0, 1, 29, 526, 7638, 97119, 1129899, 12333364, 128314460, 1285931725] := by
  native_decide

theorem bucketOverflowNumerator_cap3_values :
    List.map (bucketOverflowNumerator 3) [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] =
      [0, 0, 0, 0, 1, 36, 778, 13084, 188707, 2450848, 29489300, 334739560] := by
  native_decide

theorem bucketOverflowNumerator_table_values :
    List.ofFn bucketOverflowNumeratorCap1Table =
        List.map (bucketOverflowNumerator 1) [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] ∧
      List.ofFn bucketOverflowNumeratorCap2Table =
        List.map (bucketOverflowNumerator 2) [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] ∧
      List.ofFn bucketOverflowNumeratorCap3Table =
        List.map (bucketOverflowNumerator 3) [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] := by
  native_decide



structure DigitalTreeAnalysisBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DigitalTreeAnalysisBudgetCertificate.controlled
    (c : DigitalTreeAnalysisBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def DigitalTreeAnalysisBudgetCertificate.budgetControlled
    (c : DigitalTreeAnalysisBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def DigitalTreeAnalysisBudgetCertificate.Ready
    (c : DigitalTreeAnalysisBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def DigitalTreeAnalysisBudgetCertificate.size
    (c : DigitalTreeAnalysisBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem digitalTreeAnalysis_budgetCertificate_le_size
    (c : DigitalTreeAnalysisBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleDigitalTreeAnalysisBudgetCertificate :
    DigitalTreeAnalysisBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleDigitalTreeAnalysisBudgetCertificate.Ready := by
  constructor
  · norm_num [DigitalTreeAnalysisBudgetCertificate.controlled,
      sampleDigitalTreeAnalysisBudgetCertificate]
  · norm_num [DigitalTreeAnalysisBudgetCertificate.budgetControlled,
      sampleDigitalTreeAnalysisBudgetCertificate]

example :
    sampleDigitalTreeAnalysisBudgetCertificate.certificateBudgetWindow ≤
      sampleDigitalTreeAnalysisBudgetCertificate.size := by
  apply digitalTreeAnalysis_budgetCertificate_le_size
  constructor
  · norm_num [DigitalTreeAnalysisBudgetCertificate.controlled,
      sampleDigitalTreeAnalysisBudgetCertificate]
  · norm_num [DigitalTreeAnalysisBudgetCertificate.budgetControlled,
      sampleDigitalTreeAnalysisBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleDigitalTreeAnalysisBudgetCertificate.Ready := by
  constructor
  · norm_num [DigitalTreeAnalysisBudgetCertificate.controlled,
      sampleDigitalTreeAnalysisBudgetCertificate]
  · norm_num [DigitalTreeAnalysisBudgetCertificate.budgetControlled,
      sampleDigitalTreeAnalysisBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleDigitalTreeAnalysisBudgetCertificate.certificateBudgetWindow ≤
      sampleDigitalTreeAnalysisBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List DigitalTreeAnalysisBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleDigitalTreeAnalysisBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleDigitalTreeAnalysisBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch9.DigitalTreeAnalysis
