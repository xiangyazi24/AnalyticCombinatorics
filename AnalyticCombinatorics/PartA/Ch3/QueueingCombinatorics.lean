import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartA.Ch3.QueueingCombinatorics


/-!
# Queueing and Service Combinatorics

Finite, executable checks for the ballot, Catalan, cycle-lemma, Narayana,
parking-function, and priority-queue counts appearing around Chapter III of
Flajolet and Sedgewick.
-/

/-! ## Ballot problem -/

/-- Strict ballot-count formula: candidate `A` is always ahead of `B`. -/
def strictBallotCount (a b : ℕ) : ℕ :=
  if b < a then ((a - b) * Nat.choose (a + b) a) / (a + b) else 0

/-- Numerator of the strict-ballot probability `(a-b)/(a+b)`. -/
def strictBallotProbabilityNumerator (a b : ℕ) : ℕ :=
  a - b

/-- Denominator of the strict-ballot probability `(a-b)/(a+b)`. -/
def strictBallotProbabilityDenominator (a b : ℕ) : ℕ :=
  a + b

/--
Integer form of
`P(A always ahead) = (a-b)/(a+b)` after multiplying by the denominator.
-/
def strictBallotIntegerForm (a b : ℕ) : Bool :=
  strictBallotProbabilityDenominator a b * strictBallotCount a b ==
    strictBallotProbabilityNumerator a b * Nat.choose (a + b) a

theorem strictBallot_integer_2_1 : strictBallotIntegerForm 2 1 = true := by
  native_decide

theorem strictBallot_integer_3_1 : strictBallotIntegerForm 3 1 = true := by
  native_decide

theorem strictBallot_integer_3_2 : strictBallotIntegerForm 3 2 = true := by
  native_decide

theorem strictBallot_integer_4_1 : strictBallotIntegerForm 4 1 = true := by
  native_decide

theorem strictBallot_integer_4_2 : strictBallotIntegerForm 4 2 = true := by
  native_decide

theorem strictBallot_integer_4_3 : strictBallotIntegerForm 4 3 = true := by
  native_decide

theorem strictBallot_integer_5_2 : strictBallotIntegerForm 5 2 = true := by
  native_decide

theorem strictBallot_integer_5_3 : strictBallotIntegerForm 5 3 = true := by
  native_decide

theorem strictBallot_integer_5_4 : strictBallotIntegerForm 5 4 = true := by
  native_decide

theorem strictBallot_count_2_1 : strictBallotCount 2 1 = 1 := by
  native_decide

theorem strictBallot_count_3_1 : strictBallotCount 3 1 = 2 := by
  native_decide

theorem strictBallot_count_3_2 : strictBallotCount 3 2 = 2 := by
  native_decide

theorem strictBallot_count_4_2 : strictBallotCount 4 2 = 5 := by
  native_decide

theorem strictBallot_count_5_3 : strictBallotCount 5 3 = 14 := by
  native_decide

/-! ## Catalan numbers from ballot paths -/

/-- Catalan number in central-binomial form. -/
def catalan (n : ℕ) : ℕ :=
  Nat.choose (2 * n) n / (n + 1)

/-- Catalan number in the reflection/ballot difference form. -/
def catalanBallotDifference (n : ℕ) : ℕ :=
  Nat.choose (2 * n) n - Nat.choose (2 * n) (n + 1)

/-- Integer form of `C_n = (1/(n+1)) * binom(2n,n)`. -/
def catalanCentralIntegerForm (n : ℕ) : Bool :=
  (n + 1) * catalan n == Nat.choose (2 * n) n

/-- Difference form `C_n = binom(2n,n) - binom(2n,n+1)`. -/
def catalanBallotForm (n : ℕ) : Bool :=
  catalan n == catalanBallotDifference n

theorem catalan_zero : catalan 0 = 1 := by
  native_decide

theorem catalan_one : catalan 1 = 1 := by
  native_decide

theorem catalan_two : catalan 2 = 2 := by
  native_decide

theorem catalan_three : catalan 3 = 5 := by
  native_decide

theorem catalan_four : catalan 4 = 14 := by
  native_decide

theorem catalan_five : catalan 5 = 42 := by
  native_decide

theorem catalan_six : catalan 6 = 132 := by
  native_decide

theorem catalan_central_integer_0 : catalanCentralIntegerForm 0 = true := by
  native_decide

theorem catalan_central_integer_1 : catalanCentralIntegerForm 1 = true := by
  native_decide

theorem catalan_central_integer_2 : catalanCentralIntegerForm 2 = true := by
  native_decide

theorem catalan_central_integer_3 : catalanCentralIntegerForm 3 = true := by
  native_decide

theorem catalan_central_integer_4 : catalanCentralIntegerForm 4 = true := by
  native_decide

theorem catalan_central_integer_5 : catalanCentralIntegerForm 5 = true := by
  native_decide

theorem catalan_ballot_difference_0 : catalanBallotForm 0 = true := by
  native_decide

theorem catalan_ballot_difference_1 : catalanBallotForm 1 = true := by
  native_decide

theorem catalan_ballot_difference_2 : catalanBallotForm 2 = true := by
  native_decide

theorem catalan_ballot_difference_3 : catalanBallotForm 3 = true := by
  native_decide

theorem catalan_ballot_difference_4 : catalanBallotForm 4 = true := by
  native_decide

theorem catalan_ballot_difference_5 : catalanBallotForm 5 = true := by
  native_decide

/-! ## Cycle lemma -/

/-- The `r`th cyclic shift of a finite integer list. -/
def cyclicShift (xs : List ℤ) (r : ℕ) : List ℤ :=
  (List.range xs.length).map fun i => xs.getD ((r + i) % xs.length) 0

/-- Sum of the first `m` terms of a finite integer list, with missing terms as zero. -/
def prefixSum (xs : List ℤ) (m : ℕ) : ℤ :=
  ((List.range m).map fun i => xs.getD i 0).sum

/-- Boolean form: every nonempty prefix has positive sum. -/
def allPrefixSumsPositive (xs : List ℤ) : Bool :=
  (List.range xs.length).all fun i => 0 < prefixSum xs (i + 1)

/-- Number of cyclic shifts whose nonempty prefix sums are all positive. -/
def positiveCyclicShiftCount (xs : List ℤ) : ℕ :=
  ((List.range xs.length).filter fun r => allPrefixSumsPositive (cyclicShift xs r)).length

/--
Cycle-lemma test: for these total-sum-one sequences, exactly one cyclic shift
has all nonempty partial sums positive.
-/
def cycleLemmaOnePositiveShift (xs : List ℤ) : Bool :=
  positiveCyclicShiftCount xs == 1

theorem cycleLemma_sequence_1 : cycleLemmaOnePositiveShift [1] = true := by
  native_decide

theorem cycleLemma_sequence_2 : cycleLemmaOnePositiveShift [-1, 2] = true := by
  native_decide

theorem cycleLemma_sequence_3 : cycleLemmaOnePositiveShift [1, -1, 1] = true := by
  native_decide

theorem cycleLemma_sequence_4 : cycleLemmaOnePositiveShift [-1, 1, -1, 2] = true := by
  native_decide

theorem cycleLemma_sequence_5 : cycleLemmaOnePositiveShift [2, -1, -1, 2, -1] = true := by
  native_decide

theorem cycleLemma_sequence_6 : cycleLemmaOnePositiveShift [-2, 3, -1, 1] = true := by
  native_decide

theorem positive_shift_count_sequence_4 :
    positiveCyclicShiftCount [-1, 1, -1, 2] = 1 := by
  native_decide

theorem positive_shift_count_sequence_5 :
    positiveCyclicShiftCount [2, -1, -1, 2, -1] = 1 := by
  native_decide

/-! ## Narayana numbers -/

/-- Narayana number `N(n,k) = (1/n) * binom(n,k) * binom(n,k-1)`. -/
def narayana (n k : ℕ) : ℕ :=
  if n = 0 then 0 else (Nat.choose n k * Nat.choose n (k - 1)) / n

/-- Integer form of the Narayana formula, avoiding division. -/
def narayanaIntegerForm (n k value : ℕ) : Bool :=
  n * value == Nat.choose n k * Nat.choose n (k - 1)

theorem narayana_3_1 : narayana 3 1 = 1 := by
  native_decide

theorem narayana_3_2 : narayana 3 2 = 3 := by
  native_decide

theorem narayana_3_3 : narayana 3 3 = 1 := by
  native_decide

theorem narayana_4_1 : narayana 4 1 = 1 := by
  native_decide

theorem narayana_4_2 : narayana 4 2 = 6 := by
  native_decide

theorem narayana_4_3 : narayana 4 3 = 6 := by
  native_decide

theorem narayana_4_4 : narayana 4 4 = 1 := by
  native_decide

theorem narayana_5_1 : narayana 5 1 = 1 := by
  native_decide

theorem narayana_5_2 : narayana 5 2 = 10 := by
  native_decide

theorem narayana_5_3 : narayana 5 3 = 20 := by
  native_decide

theorem narayana_5_4 : narayana 5 4 = 10 := by
  native_decide

theorem narayana_5_5 : narayana 5 5 = 1 := by
  native_decide

theorem narayana_row_3_sum :
    narayana 3 1 + narayana 3 2 + narayana 3 3 = catalan 3 := by
  native_decide

theorem narayana_row_4_sum :
    narayana 4 1 + narayana 4 2 + narayana 4 3 + narayana 4 4 = catalan 4 := by
  native_decide

theorem narayana_row_5_sum :
    narayana 5 1 + narayana 5 2 + narayana 5 3 + narayana 5 4 + narayana 5 5 =
      catalan 5 := by
  native_decide

theorem narayana_3_2_integer : narayanaIntegerForm 3 2 3 = true := by
  native_decide

theorem narayana_4_2_integer : narayanaIntegerForm 4 2 6 = true := by
  native_decide

theorem narayana_5_3_integer : narayanaIntegerForm 5 3 20 = true := by
  native_decide

/-! ## Parking functions -/

/-- Parking functions on `[n]`, in the `n^(n-1)` convention. -/
def parkingFunctionsOnCount (n : ℕ) : ℕ :=
  n ^ (n - 1)

theorem parkingFunctionsOn_one : parkingFunctionsOnCount 1 = 1 := by
  native_decide

theorem parkingFunctionsOn_two : parkingFunctionsOnCount 2 = 2 := by
  native_decide

theorem parkingFunctionsOn_three : parkingFunctionsOnCount 3 = 9 := by
  native_decide

theorem parkingFunctionsOn_four : parkingFunctionsOnCount 4 = 64 := by
  native_decide

theorem parkingFunctionsOn_five : parkingFunctionsOnCount 5 = 625 := by
  native_decide

/-! ## Priority queue sizes and Catalan numbers -/

/--
Size traces of a priority queue with `n` insertions and `n` removals are Dyck
paths of semilength `n`, hence Catalan.
-/
def priorityQueueSizeTraceCount (n : ℕ) : ℕ :=
  catalan n

/-- Integer form of the priority-queue/Catalan relationship. -/
def priorityQueueCatalanIntegerForm (n : ℕ) : Bool :=
  (n + 1) * priorityQueueSizeTraceCount n == Nat.choose (2 * n) n

theorem priorityQueueSizeTrace_zero : priorityQueueSizeTraceCount 0 = 1 := by
  native_decide

theorem priorityQueueSizeTrace_one : priorityQueueSizeTraceCount 1 = 1 := by
  native_decide

theorem priorityQueueSizeTrace_two : priorityQueueSizeTraceCount 2 = 2 := by
  native_decide

theorem priorityQueueSizeTrace_three : priorityQueueSizeTraceCount 3 = 5 := by
  native_decide

theorem priorityQueueSizeTrace_four : priorityQueueSizeTraceCount 4 = 14 := by
  native_decide

theorem priorityQueueSizeTrace_five : priorityQueueSizeTraceCount 5 = 42 := by
  native_decide

theorem priorityQueue_catalan_integer_1 : priorityQueueCatalanIntegerForm 1 = true := by
  native_decide

theorem priorityQueue_catalan_integer_2 : priorityQueueCatalanIntegerForm 2 = true := by
  native_decide

theorem priorityQueue_catalan_integer_3 : priorityQueueCatalanIntegerForm 3 = true := by
  native_decide

theorem priorityQueue_catalan_integer_4 : priorityQueueCatalanIntegerForm 4 = true := by
  native_decide

theorem priorityQueue_catalan_integer_5 : priorityQueueCatalanIntegerForm 5 = true := by
  native_decide



structure QueueingCombinatoricsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def QueueingCombinatoricsBudgetCertificate.controlled
    (c : QueueingCombinatoricsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def QueueingCombinatoricsBudgetCertificate.budgetControlled
    (c : QueueingCombinatoricsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def QueueingCombinatoricsBudgetCertificate.Ready
    (c : QueueingCombinatoricsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def QueueingCombinatoricsBudgetCertificate.size
    (c : QueueingCombinatoricsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem queueingCombinatorics_budgetCertificate_le_size
    (c : QueueingCombinatoricsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleQueueingCombinatoricsBudgetCertificate :
    QueueingCombinatoricsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleQueueingCombinatoricsBudgetCertificate.Ready := by
  constructor
  · norm_num [QueueingCombinatoricsBudgetCertificate.controlled,
      sampleQueueingCombinatoricsBudgetCertificate]
  · norm_num [QueueingCombinatoricsBudgetCertificate.budgetControlled,
      sampleQueueingCombinatoricsBudgetCertificate]

example :
    sampleQueueingCombinatoricsBudgetCertificate.certificateBudgetWindow ≤
      sampleQueueingCombinatoricsBudgetCertificate.size := by
  apply queueingCombinatorics_budgetCertificate_le_size
  constructor
  · norm_num [QueueingCombinatoricsBudgetCertificate.controlled,
      sampleQueueingCombinatoricsBudgetCertificate]
  · norm_num [QueueingCombinatoricsBudgetCertificate.budgetControlled,
      sampleQueueingCombinatoricsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleQueueingCombinatoricsBudgetCertificate.Ready := by
  constructor
  · norm_num [QueueingCombinatoricsBudgetCertificate.controlled,
      sampleQueueingCombinatoricsBudgetCertificate]
  · norm_num [QueueingCombinatoricsBudgetCertificate.budgetControlled,
      sampleQueueingCombinatoricsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleQueueingCombinatoricsBudgetCertificate.certificateBudgetWindow ≤
      sampleQueueingCombinatoricsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List QueueingCombinatoricsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleQueueingCombinatoricsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleQueueingCombinatoricsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch3.QueueingCombinatorics
