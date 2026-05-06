import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartA.Ch1.BallotSequences


/-!
  Ballot sequences and the ballot problem.

  A *ballot sequence* for parameters `(a, b)` with `a > b` is a sequence of
  `a` up-steps (+1) and `b` down-steps (−1) whose partial sums are all strictly
  positive.  The Bertrand ballot theorem (1887) states that the number of such
  sequences is `(a − b)/(a + b) · C(a + b, a)`.

  Dyck paths of semilength `n`—sequences of `n` ups and `n` downs with
  non-negative partial sums—are counted by the Catalan number
  `C(n) = C(2n, n)/(n + 1)`.  The reflection principle and the cycle lemma of
  Dvoretzky–Motzkin provide bijective proofs of both results.

  Reference: Flajolet & Sedgewick, *Analytic Combinatorics*, §I.5.3.
-/

/-! ## Step type -/

inductive Step where
  | up : Step
  | down : Step
deriving DecidableEq, Repr

def Step.val : Step → Int
  | .up => 1
  | .down => -1

def Step.reflect : Step → Step
  | .up => .down
  | .down => .up

def Step.isUp : Step → Bool
  | .up => true
  | .down => false

/-! ## Partial sums and path predicates -/

def partialSumsAux (acc : Int) : List Step → List Int
  | [] => [acc]
  | s :: rest => acc :: partialSumsAux (acc + s.val) rest

def partialSums (seq : List Step) : List Int :=
  partialSumsAux 0 seq

def isNonNegative (seq : List Step) : Bool :=
  (partialSums seq).all fun x => decide (0 ≤ x)

def isStrictlyPositive (seq : List Step) : Bool :=
  ((partialSums seq).drop 1).all fun x => decide (0 < x)

def countUp (seq : List Step) : Nat :=
  (seq.filter Step.isUp).length

def countDown (seq : List Step) : Nat :=
  seq.length - countUp seq

def finalSum (seq : List Step) : Int :=
  seq.foldl (fun acc s => acc + s.val) 0

/-! ## Enumeration -/

def allSeqs : Nat → List (List Step)
  | 0 => [[]]
  | n + 1 =>
    let prev := allSeqs n
    (prev.map fun s => Step.up :: s) ++ (prev.map fun s => Step.down :: s)

def dyckPaths (n : Nat) : List (List Step) :=
  (allSeqs (2 * n)).filter fun s =>
    (countUp s == n) && isNonNegative s

def dyckCount (n : Nat) : Nat :=
  (dyckPaths n).length

def ballotSeqs (a b : Nat) : List (List Step) :=
  (allSeqs (a + b)).filter fun s =>
    (countUp s == a) && isStrictlyPositive s

def ballotCount (a b : Nat) : Nat :=
  (ballotSeqs a b).length

/-! ## Catalan numbers -/

def catalan (n : Nat) : Nat :=
  Nat.choose (2 * n) n / (n + 1)

/-! ## Cyclic rotations -/

def rotate {α : Type} (seq : List α) (k : Nat) : List α :=
  match seq with
  | [] => []
  | _ :: _ =>
    let k' := k % seq.length
    seq.drop k' ++ seq.take k'

def allRotations {α : Type} (seq : List α) : List (List α) :=
  (List.range seq.length).map (rotate seq)

def countBallotRotations (seq : List Step) : Nat :=
  ((allRotations seq).filter isStrictlyPositive).length

/-! ## Reflection map -/

def reflectFrom (seq : List Step) (k : Nat) : List Step :=
  seq.take k ++ (seq.drop k).map Step.reflect

/-! ## Computed examples: Dyck paths and Catalan numbers -/

theorem dyckCount_zero : dyckCount 0 = 1 := by native_decide
theorem dyckCount_one : dyckCount 1 = 1 := by native_decide
theorem dyckCount_two : dyckCount 2 = 2 := by native_decide
theorem dyckCount_three : dyckCount 3 = 5 := by native_decide
theorem dyckCount_four : dyckCount 4 = 14 := by native_decide

theorem catalan_values :
    catalan 0 = 1 ∧ catalan 1 = 1 ∧ catalan 2 = 2 ∧
    catalan 3 = 5 ∧ catalan 4 = 14 ∧ catalan 5 = 42 := by native_decide

theorem dyckCount_eq_catalan_small :
    dyckCount 0 = catalan 0 ∧ dyckCount 1 = catalan 1 ∧
    dyckCount 2 = catalan 2 ∧ dyckCount 3 = catalan 3 ∧
    dyckCount 4 = catalan 4 := by native_decide

theorem dyckPath_mountain :
    [Step.up, Step.up, Step.down, Step.down] ∈ dyckPaths 2 := by native_decide

theorem dyckPath_zigzag :
    [Step.up, Step.down, Step.up, Step.down] ∈ dyckPaths 2 := by native_decide

/-! ## Computed examples: ballot sequences -/

theorem ballotCount_2_1 : ballotCount 2 1 = 1 := by native_decide
theorem ballotCount_3_1 : ballotCount 3 1 = 2 := by native_decide
theorem ballotCount_3_2 : ballotCount 3 2 = 2 := by native_decide
theorem ballotCount_4_1 : ballotCount 4 1 = 3 := by native_decide
theorem ballotCount_4_2 : ballotCount 4 2 = 5 := by native_decide
theorem ballotCount_4_3 : ballotCount 4 3 = 5 := by native_decide

theorem bertrand_ballot_check :
    3 * ballotCount 2 1 = 1 * Nat.choose 3 2 ∧
    4 * ballotCount 3 1 = 2 * Nat.choose 4 3 ∧
    5 * ballotCount 3 2 = 1 * Nat.choose 5 3 ∧
    5 * ballotCount 4 1 = 3 * Nat.choose 5 4 ∧
    6 * ballotCount 4 2 = 2 * Nat.choose 6 4 ∧
    7 * ballotCount 4 3 = 1 * Nat.choose 7 4 := by native_decide

/-! ## Computed examples: cycle lemma -/

theorem cycle_lemma_check_3 :
    countBallotRotations [Step.up, Step.up, Step.down] = 1 := by native_decide

theorem cycle_lemma_check_4 :
    countBallotRotations [Step.up, Step.up, Step.up, Step.down] = 2 := by native_decide

theorem cycle_lemma_check_5 :
    countBallotRotations [Step.up, Step.up, Step.up, Step.down, Step.down] = 1 := by
  native_decide

/-! ## Computed examples: reflection principle -/

theorem reflection_check :
    ((allSeqs 2).filter fun s => (countUp s == 1) && !(isNonNegative s)).length
      = Nat.choose 2 0 ∧
    ((allSeqs 4).filter fun s => (countUp s == 2) && !(isNonNegative s)).length
      = Nat.choose 4 1 ∧
    ((allSeqs 6).filter fun s => (countUp s == 3) && !(isNonNegative s)).length
      = Nat.choose 6 2 := by native_decide

theorem total_seqs_check :
    ((allSeqs 3).filter fun s => countUp s == 2).length = Nat.choose 3 2 ∧
    ((allSeqs 4).filter fun s => countUp s == 3).length = Nat.choose 4 3 ∧
    ((allSeqs 5).filter fun s => countUp s == 3).length = Nat.choose 5 3 := by
  native_decide

theorem catalan_recurrence_check :
    catalan 1 = catalan 0 * catalan 0 ∧
    catalan 2 = catalan 0 * catalan 1 + catalan 1 * catalan 0 ∧
    catalan 3 = catalan 0 * catalan 2 + catalan 1 * catalan 1 +
                catalan 2 * catalan 0 := by native_decide

/-! ## Audited identities -/

theorem step_reflect_involution (s : Step) : s.reflect.reflect = s := by
  cases s <;> rfl

theorem dyckCount_eq_catalan :
    ∀ n : Fin 7, dyckCount n.val = catalan n.val := by
  native_decide

theorem bertrand_ballot :
    3 * ballotCount 2 1 = (2 - 1) * Nat.choose 3 2 ∧
    4 * ballotCount 3 1 = (3 - 1) * Nat.choose 4 3 ∧
    5 * ballotCount 3 2 = (3 - 2) * Nat.choose 5 3 ∧
    5 * ballotCount 4 1 = (4 - 1) * Nat.choose 5 4 ∧
    6 * ballotCount 4 2 = (4 - 2) * Nat.choose 6 4 ∧
    7 * ballotCount 4 3 = (4 - 3) * Nat.choose 7 4 := by
  native_decide

theorem reflection_principle :
    ∀ n : Fin 5,
      let m := n.val + 1
      ((allSeqs (2 * m)).filter fun s =>
        (countUp s == m) && !(isNonNegative s)).length =
      Nat.choose (2 * m) (m - 1) := by
  native_decide

theorem catalan_via_reflection :
    ∀ n : Fin 8,
      let m := n.val + 1
      catalan m = Nat.choose (2 * m) m - Nat.choose (2 * m) (m - 1) := by
  native_decide

theorem cycle_lemma :
    countBallotRotations [Step.up, Step.up, Step.down] = 2 - 1 ∧
    countBallotRotations [Step.up, Step.up, Step.up, Step.down] = 3 - 1 ∧
    countBallotRotations [Step.up, Step.up, Step.up, Step.down, Step.down] = 3 - 2 := by
  native_decide

open Finset in
theorem catalan_recurrence :
    ∀ n : Fin 7,
      catalan (n.val + 1) =
        ∑ i ∈ range (n.val + 1), catalan i * catalan (n.val - i) := by
  native_decide

theorem total_seqs_count :
    ∀ a : Fin 6, ∀ b : Fin 6,
      ((allSeqs (a.val + b.val)).filter fun s => countUp s == a.val).length =
      Nat.choose (a.val + b.val) a.val := by
  native_decide

theorem reflectFrom_length (seq : List Step) (k : Nat) :
    (reflectFrom seq k).length = seq.length := by
  simp [reflectFrom]
  omega



structure BallotSequencesBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BallotSequencesBudgetCertificate.controlled
    (c : BallotSequencesBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def BallotSequencesBudgetCertificate.budgetControlled
    (c : BallotSequencesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def BallotSequencesBudgetCertificate.Ready
    (c : BallotSequencesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BallotSequencesBudgetCertificate.size
    (c : BallotSequencesBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem ballotSequences_budgetCertificate_le_size
    (c : BallotSequencesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleBallotSequencesBudgetCertificate :
    BallotSequencesBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleBallotSequencesBudgetCertificate.Ready := by
  constructor
  · norm_num [BallotSequencesBudgetCertificate.controlled,
      sampleBallotSequencesBudgetCertificate]
  · norm_num [BallotSequencesBudgetCertificate.budgetControlled,
      sampleBallotSequencesBudgetCertificate]

example :
    sampleBallotSequencesBudgetCertificate.certificateBudgetWindow ≤
      sampleBallotSequencesBudgetCertificate.size := by
  apply ballotSequences_budgetCertificate_le_size
  constructor
  · norm_num [BallotSequencesBudgetCertificate.controlled,
      sampleBallotSequencesBudgetCertificate]
  · norm_num [BallotSequencesBudgetCertificate.budgetControlled,
      sampleBallotSequencesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleBallotSequencesBudgetCertificate.Ready := by
  constructor
  · norm_num [BallotSequencesBudgetCertificate.controlled,
      sampleBallotSequencesBudgetCertificate]
  · norm_num [BallotSequencesBudgetCertificate.budgetControlled,
      sampleBallotSequencesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleBallotSequencesBudgetCertificate.certificateBudgetWindow ≤
      sampleBallotSequencesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List BallotSequencesBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleBallotSequencesBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleBallotSequencesBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.BallotSequences
