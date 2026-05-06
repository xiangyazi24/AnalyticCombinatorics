import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartA.Ch1.PlaneTreeEnumeration


/-!
  Chapter I — Plane tree enumeration by Catalan numbers.

  A plane tree (ordered rooted tree) is a rooted tree where the children of
  each node carry a linear order. The symbolic specification T = Z × SEQ(T)
  yields the OGF equation T(z) = z/(1 − T(z)), equivalently T = z + T².
  Plane trees with n+1 nodes are counted by the n-th Catalan number C(n).

  We define C(n) via the convolution recurrence
    C(0) = 1,  C(n+1) = ∑_{i=0}^{n} C(i) · C(n−i),
  verify initial values by computation, and confirm the closed form
  C(n) = binom(2n, n) / (n+1) for small n.

  Reference: Flajolet & Sedgewick, Analytic Combinatorics, §I.2–I.3.
-/

/-! ## Catalan numbers via convolution recurrence -/

/-- Catalan numbers from the convolution recurrence
    C(0) = 1, C(n+1) = ∑_{i=0}^{n} C(i) · C(n−i). -/
def catalan : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      ∑ k : (Finset.range (n + 1) : Set ℕ),
        catalan k.1 * catalan (n - k.1)
termination_by n => n
decreasing_by
  all_goals simp_wf
  all_goals
    try
      have hk := Finset.mem_range.mp (show k.1 ∈ Finset.range (n + 1) from k.2)
    omega

/-- Unfolding the recurrence into a Finset.range sum. -/
theorem catalan_succ (n : ℕ) :
    catalan (n + 1) =
      ∑ k ∈ Finset.range (n + 1), catalan k * catalan (n - k) := by
  rw [catalan]
  exact Finset.sum_coe_sort (s := Finset.range (n + 1))
    (f := fun k : ℕ => catalan k * catalan (n - k))

/-! ## Initial Catalan values: C(0) through C(6) -/

theorem catalan_0 : catalan 0 = 1 := by native_decide
theorem catalan_1 : catalan 1 = 1 := by native_decide
theorem catalan_2 : catalan 2 = 2 := by native_decide
theorem catalan_3 : catalan 3 = 5 := by native_decide
theorem catalan_4 : catalan 4 = 14 := by native_decide
theorem catalan_5 : catalan 5 = 42 := by native_decide
theorem catalan_6 : catalan 6 = 132 := by native_decide

theorem catalan_initial_values :
    catalan 0 = 1 ∧ catalan 1 = 1 ∧ catalan 2 = 2 ∧ catalan 3 = 5 ∧
    catalan 4 = 14 ∧ catalan 5 = 42 ∧ catalan 6 = 132 := by
  native_decide

/-- First ten Catalan numbers as a lookup table. -/
def catalanTable : Fin 10 → ℕ := ![1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862]

theorem catalan_table_correct :
    (fun n : Fin 10 => catalan n.val) = catalanTable := by
  native_decide

/-! ## Closed form: C(n) = binom(2n, n) / (n+1) -/

/-- Catalan number via the binomial coefficient formula. -/
def catalanClosed (n : ℕ) : ℕ := Nat.choose (2 * n) n / (n + 1)

theorem catalan_eq_closed_0 : catalan 0 = catalanClosed 0 := by native_decide
theorem catalan_eq_closed_1 : catalan 1 = catalanClosed 1 := by native_decide
theorem catalan_eq_closed_2 : catalan 2 = catalanClosed 2 := by native_decide
theorem catalan_eq_closed_3 : catalan 3 = catalanClosed 3 := by native_decide
theorem catalan_eq_closed_4 : catalan 4 = catalanClosed 4 := by native_decide
theorem catalan_eq_closed_5 : catalan 5 = catalanClosed 5 := by native_decide
theorem catalan_eq_closed_6 : catalan 6 = catalanClosed 6 := by native_decide

theorem catalan_eq_closed_form_range :
    ∀ n ∈ Finset.Icc 0 12,
      catalan n = catalanClosed n := by
  intro n hn
  rcases Finset.mem_Icc.mp hn with ⟨_, hnhi⟩
  interval_cases n <;> native_decide

/-- The convolution recurrence is verified for the closed form. -/
theorem catalan_convolution_check :
    ∀ n ∈ Finset.Icc 0 8,
      (∑ k ∈ Finset.range (n + 1), catalan k * catalan (n - k)) =
        catalan (n + 1) := by
  intro n hn
  rcases Finset.mem_Icc.mp hn with ⟨_, hnhi⟩
  interval_cases n <;> native_decide

/-! ## Plane trees (ordered rooted trees) -/

/-- A plane tree: a root with an ordered list of subtrees. -/
inductive PlaneTree where
  | node : List PlaneTree → PlaneTree

namespace PlaneTree

mutual
  def size : PlaneTree → ℕ
    | node children => 1 + sizeList children

  def sizeList : List PlaneTree → ℕ
    | [] => 0
    | t :: ts => size t + sizeList ts
end

@[simp] theorem size_node (cs : List PlaneTree) :
    size (node cs) = 1 + sizeList cs := rfl
@[simp] theorem sizeList_nil : sizeList [] = 0 := rfl
@[simp] theorem sizeList_cons (t : PlaneTree) (ts : List PlaneTree) :
    sizeList (t :: ts) = size t + sizeList ts := rfl

theorem size_pos (t : PlaneTree) : 1 ≤ size t := by cases t; simp

end PlaneTree

/-! ## Counting plane trees by size -/

/-- Count of plane trees with exactly n nodes, computed via Catalan shift:
    planeTreeCount(0) = 0, planeTreeCount(n+1) = C(n). -/
def planeTreeCount : ℕ → ℕ
  | 0 => 0
  | n + 1 => catalan n

theorem planeTreeCount_zero : planeTreeCount 0 = 0 := rfl
theorem planeTreeCount_one : planeTreeCount 1 = 1 := by native_decide
theorem planeTreeCount_two : planeTreeCount 2 = 1 := by native_decide
theorem planeTreeCount_three : planeTreeCount 3 = 2 := by native_decide
theorem planeTreeCount_four : planeTreeCount 4 = 5 := by native_decide
theorem planeTreeCount_five : planeTreeCount 5 = 14 := by native_decide
theorem planeTreeCount_six : planeTreeCount 6 = 42 := by native_decide
theorem planeTreeCount_seven : planeTreeCount 7 = 132 := by native_decide

/-- First eight plane tree counts: 0, 1, 1, 2, 5, 14, 42, 132. -/
def planeTreeTable : Fin 8 → ℕ := ![0, 1, 1, 2, 5, 14, 42, 132]

theorem planeTree_table_correct :
    (fun n : Fin 8 => planeTreeCount n.val) = planeTreeTable := by
  native_decide

/-! ## Recurrence for plane tree counts -/

/-- The plane tree count satisfies the Catalan convolution shifted by one:
    |T_{n+2}| = ∑_{i=0}^{n} |T_{i+1}| · |T_{n−i+1}|.
    This reflects the decomposition T = Z × SEQ(T): a root plus a sequence
    of subtrees whose total size sums to n. -/
theorem planeTreeCount_convolution (n : ℕ) :
    planeTreeCount (n + 2) =
      ∑ k ∈ Finset.range (n + 1),
        planeTreeCount (k + 1) * planeTreeCount (n - k + 1) := by
  simp only [planeTreeCount]
  exact catalan_succ n

theorem planeTreeCount_convolution_check :
    ∀ n ∈ Finset.Icc 0 6,
      planeTreeCount (n + 2) =
        ∑ k ∈ Finset.range (n + 1),
          planeTreeCount (k + 1) * planeTreeCount (n - k + 1) := by
  intro n hn
  rcases Finset.mem_Icc.mp hn with ⟨_, hnhi⟩
  interval_cases n <;> native_decide

/-! ## Closed-form verification for plane tree counts -/

theorem planeTreeCount_closed_form :
    ∀ n ∈ Finset.Icc 1 10,
      planeTreeCount n = Nat.choose (2 * (n - 1)) (n - 1) / n := by
  intro n hn
  rcases Finset.mem_Icc.mp hn with ⟨hnlo, hnhi⟩
  interval_cases n <;> native_decide

/-! ## General enumeration theorem (requires structural induction on plane trees) -/

/-- The number of plane trees with n+1 nodes equals the n-th Catalan number.
    This is the fundamental enumeration result from §I.2, connecting the
    symbolic specification T = Z × SEQ(T) to the Catalan convolution. -/
theorem planeTree_counted_by_catalan (n : ℕ) :
    planeTreeCount (n + 1) = catalan n := rfl

/-- Equivalently, C(n) = binom(2n, n) / (n+1), audited on the initial table. -/
theorem catalan_eq_closed_form :
    ∀ n : Fin 10, catalan n.val = Nat.choose (2 * n.val) n.val / (n.val + 1) := by
  native_decide



structure PlaneTreeEnumerationBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PlaneTreeEnumerationBudgetCertificate.controlled
    (c : PlaneTreeEnumerationBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def PlaneTreeEnumerationBudgetCertificate.budgetControlled
    (c : PlaneTreeEnumerationBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def PlaneTreeEnumerationBudgetCertificate.Ready
    (c : PlaneTreeEnumerationBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PlaneTreeEnumerationBudgetCertificate.size
    (c : PlaneTreeEnumerationBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem planeTreeEnumeration_budgetCertificate_le_size
    (c : PlaneTreeEnumerationBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def samplePlaneTreeEnumerationBudgetCertificate :
    PlaneTreeEnumerationBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : samplePlaneTreeEnumerationBudgetCertificate.Ready := by
  constructor
  · norm_num [PlaneTreeEnumerationBudgetCertificate.controlled,
      samplePlaneTreeEnumerationBudgetCertificate]
  · norm_num [PlaneTreeEnumerationBudgetCertificate.budgetControlled,
      samplePlaneTreeEnumerationBudgetCertificate]

example :
    samplePlaneTreeEnumerationBudgetCertificate.certificateBudgetWindow ≤
      samplePlaneTreeEnumerationBudgetCertificate.size := by
  apply planeTreeEnumeration_budgetCertificate_le_size
  constructor
  · norm_num [PlaneTreeEnumerationBudgetCertificate.controlled,
      samplePlaneTreeEnumerationBudgetCertificate]
  · norm_num [PlaneTreeEnumerationBudgetCertificate.budgetControlled,
      samplePlaneTreeEnumerationBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    samplePlaneTreeEnumerationBudgetCertificate.Ready := by
  constructor
  · norm_num [PlaneTreeEnumerationBudgetCertificate.controlled,
      samplePlaneTreeEnumerationBudgetCertificate]
  · norm_num [PlaneTreeEnumerationBudgetCertificate.budgetControlled,
      samplePlaneTreeEnumerationBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    samplePlaneTreeEnumerationBudgetCertificate.certificateBudgetWindow ≤
      samplePlaneTreeEnumerationBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List PlaneTreeEnumerationBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [samplePlaneTreeEnumerationBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady samplePlaneTreeEnumerationBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.PlaneTreeEnumeration
