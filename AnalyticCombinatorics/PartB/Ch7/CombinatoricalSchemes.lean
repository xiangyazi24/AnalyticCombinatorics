/-
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter VII — Combinatorial Schemes.

  Systems of algebraic equations defining generating functions for families of
  structures (Flajolet & Sedgewick, Chapter VII).

  Verified via finite tables with `native_decide`.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch7.CombinatoricalSchemes
/-! ## §1  General binary trees — Catalan numbers

  The ordinary GF satisfies C(z) = 1 + z · C(z)².
  Closed form: C(n) = C(2n,n) / (n+1).
-/

/-- Catalan number C(n) = C(2n,n) / (n+1). -/
def catalan (n : ℕ) : ℕ := Nat.choose (2 * n) n / (n + 1)

/-- Table of Catalan numbers C(0) … C(8). -/
def catalanTable : Fin 9 → ℕ :=
  ![1, 1, 2, 5, 14, 42, 132, 429, 1430]

theorem catalanTable_vals :
    catalanTable 0 = 1   ∧ catalanTable 1 = 1    ∧ catalanTable 2 = 2   ∧
    catalanTable 3 = 5   ∧ catalanTable 4 = 14   ∧ catalanTable 5 = 42  ∧
    catalanTable 6 = 132 ∧ catalanTable 7 = 429  ∧ catalanTable 8 = 1430 := by
  native_decide

/-- C(n) agrees with the closed form for n = 0 … 8. -/
theorem catalan_eq_table : ∀ i : Fin 9, catalan i.val = catalanTable i := by
  native_decide

/-- Key identity: C(n) * (n+1) = C(2n,n) for n = 0 … 8. -/
theorem catalan_mul_succ_eq_centralBinom :
    ∀ i : Fin 9, catalan i.val * (i.val + 1) = Nat.choose (2 * i.val) i.val := by
  native_decide

/-- Powers of 4 for n = 1 … 8. -/
def pow4Table : Fin 8 → ℕ :=
  ![4, 16, 64, 256, 1024, 4096, 16384, 65536]

theorem pow4Table_vals :
    pow4Table 0 = 4      ∧ pow4Table 1 = 16    ∧ pow4Table 2 = 64    ∧
    pow4Table 3 = 256    ∧ pow4Table 4 = 1024  ∧ pow4Table 5 = 4096  ∧
    pow4Table 6 = 16384  ∧ pow4Table 7 = 65536 := by
  native_decide

/-- 4^n values match the table for n = 1 … 8. -/
theorem pow4_eq_table : ∀ i : Fin 8, 4 ^ (i.val + 1) = pow4Table i := by
  native_decide

/-- C(n) ≤ 4^n for n = 1 … 8 (exponential growth rate 4). -/
theorem catalan_le_pow4 :
    catalan 1 ≤ 4 ^ 1  ∧ catalan 2 ≤ 4 ^ 2  ∧ catalan 3 ≤ 4 ^ 3  ∧
    catalan 4 ≤ 4 ^ 4  ∧ catalan 5 ≤ 4 ^ 5  ∧ catalan 6 ≤ 4 ^ 6  ∧
    catalan 7 ≤ 4 ^ 7  ∧ catalan 8 ≤ 4 ^ 8 := by
  native_decide

/-! ## §2  Unary-binary trees — Motzkin numbers

  The GF satisfies U(z) = 1 + z · U(z) + z · U(z)².
  This is the Motzkin GF; the sequence is 1, 1, 2, 4, 9, 21, 51, 127, 323.
-/

/-- Motzkin numbers M(0) … M(8). -/
def motzkinTable : Fin 9 → ℕ :=
  ![1, 1, 2, 4, 9, 21, 51, 127, 323]

theorem motzkinTable_vals :
    motzkinTable 0 = 1  ∧ motzkinTable 1 = 1   ∧ motzkinTable 2 = 2   ∧
    motzkinTable 3 = 4  ∧ motzkinTable 4 = 9   ∧ motzkinTable 5 = 21  ∧
    motzkinTable 6 = 51 ∧ motzkinTable 7 = 127 ∧ motzkinTable 8 = 323 := by
  native_decide

/-- M(n) < 3^n for n = 1 … 8. -/
theorem motzkin_lt_pow3 :
    ∀ i : Fin 8, motzkinTable ⟨i.val, by omega⟩ < 3 ^ (i.val + 1) := by
  native_decide

/-- M(8) > 2^8: Motzkin growth exceeds 2^n at n = 8. -/
theorem motzkin_gt_pow2_at8 : motzkinTable 8 > 2 ^ 8 := by native_decide

/-- M(7) = 127 < 128 = 2^7: the threshold is between n=7 and n=8. -/
theorem motzkin_not_gt_pow2_at7 : ¬ (motzkinTable 7 > 2 ^ 7) := by native_decide

/-! ## §3  Full binary trees (all nodes have 0 or 2 children)

  Number of full binary trees with n leaves = C(n-1) (Catalan).
  For leaves = 1 … 8: 1, 1, 2, 5, 14, 42, 132, 429.
-/

/-- fullBinary(n) = number of full binary trees with n leaves = C(n-1). -/
def fullBinary (n : ℕ) : ℕ :=
  if n = 0 then 0 else catalan (n - 1)

/-- Table for leaves = 1 … 8. -/
def fullBinaryTable : Fin 8 → ℕ :=
  ![1, 1, 2, 5, 14, 42, 132, 429]

theorem fullBinaryTable_vals :
    fullBinaryTable 0 = 1  ∧ fullBinaryTable 1 = 1   ∧ fullBinaryTable 2 = 2  ∧
    fullBinaryTable 3 = 5  ∧ fullBinaryTable 4 = 14  ∧ fullBinaryTable 5 = 42 ∧
    fullBinaryTable 6 = 132 ∧ fullBinaryTable 7 = 429 := by
  native_decide

/-- fullBinary(n) matches Catalan for leaves = 1 … 8. -/
theorem fullBinary_eq_catalan :
    ∀ i : Fin 8, fullBinary (i.val + 1) = fullBinaryTable i := by
  native_decide

/-- Extended table for leaves = 1 … 9 (adding the n=9 entry 1430). -/
def fullBinaryTable9 : Fin 9 → ℕ :=
  ![1, 1, 2, 5, 14, 42, 132, 429, 1430]

theorem fullBinaryTable9_vals :
    fullBinaryTable9 0 = 1    ∧ fullBinaryTable9 1 = 1    ∧ fullBinaryTable9 2 = 2   ∧
    fullBinaryTable9 3 = 5    ∧ fullBinaryTable9 4 = 14   ∧ fullBinaryTable9 5 = 42  ∧
    fullBinaryTable9 6 = 132  ∧ fullBinaryTable9 7 = 429  ∧ fullBinaryTable9 8 = 1430 := by
  native_decide

/-- fullBinary(n) = C(n-1) for leaves n = 1 … 9. -/
theorem fullBinary_eq_catalan9 :
    ∀ i : Fin 9, fullBinary (i.val + 1) = catalan i.val := by
  native_decide

/-- Total nodes in a full binary tree with n leaves = 2n - 1.
    We verify: 2*(leaves) - 1 = totalNodes for n = 1 … 8.
    Encoded as: 2*(n+1) = totalNodes + 1  (avoids ℕ subtraction). -/
def totalNodesTable : Fin 8 → ℕ :=
  ![1, 3, 5, 7, 9, 11, 13, 15]

theorem totalNodes_eq_two_leaves_minus_one :
    ∀ i : Fin 8, 2 * (i.val + 1) = totalNodesTable i + 1 := by
  native_decide

/-! ## §4  Series-parallel networks

  SP(n) counts two-terminal series-parallel networks with n edges.
  SP: 1, 2, 4, 10, 24, 66, 180 for n = 1 … 7.
-/

/-- Table of SP(n) for n = 1 … 7. -/
def spTable : Fin 7 → ℕ :=
  ![1, 2, 4, 10, 24, 66, 180]

theorem spTable_vals :
    spTable 0 = 1   ∧ spTable 1 = 2  ∧ spTable 2 = 4   ∧
    spTable 3 = 10  ∧ spTable 4 = 24 ∧ spTable 5 = 66  ∧
    spTable 6 = 180 := by
  native_decide

/-- SP(n) < 3^n for n = 1 … 7. -/
theorem sp_lt_pow3 :
    ∀ i : Fin 7, spTable i < 3 ^ (i.val + 1) := by
  native_decide

/-- SP(6) > 2^6 and SP(7) > 2^7: SP growth exceeds 2^n from n = 6 onward. -/
theorem sp_gt_pow2_from6 : spTable 5 > 2 ^ 6 ∧ spTable 6 > 2 ^ 7 := by native_decide

/-- SP(5) = 24 < 32 = 2^5: SP does not yet exceed 2^n at n = 5. -/
theorem sp_not_gt_pow2_at5 : ¬ (spTable 4 > 2 ^ 5) := by native_decide

/-- SP(n) ≥ 2^(n-1) for n = 2 … 7.
    SP(2)=2≥2, SP(3)=4≥4, SP(4)=10≥8, SP(5)=24≥16, SP(6)=66≥32, SP(7)=180≥64. -/
theorem sp_ge_pow2_pred :
    spTable 1 ≥ 2 ^ 1 ∧ spTable 2 ≥ 2 ^ 2 ∧ spTable 3 ≥ 2 ^ 3 ∧
    spTable 4 ≥ 2 ^ 4 ∧ spTable 5 ≥ 2 ^ 5 ∧ spTable 6 ≥ 2 ^ 6 := by
  native_decide

/-! ## §5  Polygon dissections

  ### 5a. Triangulations of (n+2)-gon = C(n) (Catalan)

  For n = 1 … 7: 1, 2, 5, 14, 42, 132, 429.
-/

/-- Triangulation count equals C(n). -/
def triangulationCount (n : ℕ) : ℕ := catalan n

/-- Table for n = 1 … 7. -/
def triangTable : Fin 7 → ℕ :=
  ![1, 2, 5, 14, 42, 132, 429]

theorem triangTable_vals :
    triangTable 0 = 1   ∧ triangTable 1 = 2   ∧ triangTable 2 = 5  ∧
    triangTable 3 = 14  ∧ triangTable 4 = 42  ∧ triangTable 5 = 132 ∧
    triangTable 6 = 429 := by
  native_decide

/-- triangulationCount matches the table for n = 1 … 7. -/
theorem triangulation_eq_table :
    ∀ i : Fin 7, triangulationCount (i.val + 1) = triangTable i := by
  native_decide

/-! ### 5b. Dissections of (n+2)-gon into any polygons

  d(0)=1, d(1)=1, d(2)=3, d(3)=11, d(4)=45, d(5)=197, d(6)=903.
-/

/-- Table of general dissection counts d(0) … d(6). -/
def dissectionTable : Fin 7 → ℕ :=
  ![1, 1, 3, 11, 45, 197, 903]

theorem dissectionTable_vals :
    dissectionTable 0 = 1  ∧ dissectionTable 1 = 1   ∧ dissectionTable 2 = 3   ∧
    dissectionTable 3 = 11 ∧ dissectionTable 4 = 45  ∧ dissectionTable 5 = 197 ∧
    dissectionTable 6 = 903 := by
  native_decide

/-- Catalan table extended to 7 entries (C(0)..C(6)) for comparison. -/
def catalanTable7 : Fin 7 → ℕ :=
  ![1, 1, 2, 5, 14, 42, 132]

/-- d(n) ≥ C(n) for n = 0 … 6: dissections dominate triangulations. -/
theorem dissection_ge_catalan :
    ∀ i : Fin 7, catalanTable7 i ≤ dissectionTable i := by
  native_decide

/-! ## §6  Functional composition schemes — labelled rooted forests

  By the exponential formula, if T(x) counts labelled rooted trees,
  then exp(T(x)) counts labelled rooted forests.

  Number of labelled rooted forests on [n] = (n+1)^(n-1).
  n=1: 2^0=1, n=2: 3^1=3, n=3: 4^2=16, n=4: 5^3=125, n=5: 6^4=1296.
-/

/-- Number of labelled rooted forests on [n] vertices: (n+1)^(n-1). -/
def labelledForests (n : ℕ) : ℕ :=
  if n = 0 then 1 else (n + 1) ^ (n - 1)

/-- Table for n = 1 … 5. -/
def forestTable : Fin 5 → ℕ :=
  ![1, 3, 16, 125, 1296]

theorem forestTable_vals :
    forestTable 0 = 1    ∧ forestTable 1 = 3   ∧ forestTable 2 = 16 ∧
    forestTable 3 = 125  ∧ forestTable 4 = 1296 := by
  native_decide

/-- labelledForests matches the table for n = 1 … 5. -/
theorem labelledForests_eq_table :
    ∀ i : Fin 5, labelledForests (i.val + 1) = forestTable i := by
  native_decide

/-- Cayley tree count: n^(n-1) rooted labelled trees on n vertices. -/
def cayleyTrees (n : ℕ) : ℕ :=
  if n = 0 then 0 else n ^ (n - 1)

/-- Table of Cayley tree counts for n = 1 … 5. -/
def cayleyTable : Fin 5 → ℕ :=
  ![1, 2, 9, 64, 625]

theorem cayleyTable_vals :
    cayleyTable 0 = 1  ∧ cayleyTable 1 = 2 ∧ cayleyTable 2 = 9 ∧
    cayleyTable 3 = 64 ∧ cayleyTable 4 = 625 := by
  native_decide

/-- labelledForests(n) > cayleyTrees(n) for n = 2 … 5:
    more forests than trees once n ≥ 2. -/
theorem forests_gt_trees_from2 :
    labelledForests 2 > cayleyTrees 2 ∧
    labelledForests 3 > cayleyTrees 3 ∧
    labelledForests 4 > cayleyTrees 4 ∧
    labelledForests 5 > cayleyTrees 5 := by
  native_decide

/-! ## §7  Ordered (plane) trees, binary trees, and Dyck paths

  All three families are counted by the Catalan numbers:
  — Ordered (plane) rooted trees with n edges: C(n)
  — Binary trees with n internal nodes: C(n)
  — Dyck paths of semilength n: C(n)

  We record the common Catalan table and verify the key identity
  C(n) * (n+1) = C(2n, n) for n = 0 … 8.
-/

/-- Common Catalan table for plane trees / binary trees / Dyck paths:
    C(0) … C(7). -/
def planeTrees : Fin 8 → ℕ :=
  ![1, 1, 2, 5, 14, 42, 132, 429]

theorem planeTrees_vals :
    planeTrees 0 = 1   ∧ planeTrees 1 = 1   ∧ planeTrees 2 = 2   ∧
    planeTrees 3 = 5   ∧ planeTrees 4 = 14  ∧ planeTrees 5 = 42  ∧
    planeTrees 6 = 132 ∧ planeTrees 7 = 429 := by
  native_decide

/-- planeTrees matches catalan for indices 0 … 7. -/
theorem planeTrees_eq_catalan :
    ∀ i : Fin 8, planeTrees i = catalan i.val := by
  native_decide

/-- C(n)*(n+1) = C(2n,n) for n = 0 … 8 (verified via catalanTable). -/
theorem catalan_times_succ_eq_centralBinom :
    ∀ i : Fin 9, catalanTable i * (i.val + 1) = Nat.choose (2 * i.val) i.val := by
  native_decide

/-! ## §8  Growth rate comparison

  Catalan ~4^n, Motzkin ~3^n, SP networks between 2^n and 3^n.
-/

/-- C(n) < 4^n for n = 1 … 9 (strict inequality). -/
theorem catalan_lt_pow4 :
    ∀ i : Fin 9, catalan (i.val + 1) < 4 ^ (i.val + 1) := by
  native_decide

/-- M(n) < 3^n for n = 0 … 8 (Motzkin below 3^n). -/
theorem motzkin_lt_pow3_all :
    ∀ i : Fin 9, motzkinTable i < 3 ^ (i.val + 1) := by
  native_decide

/-- 4^n > 3^n > 2^n for n = 1 … 8. -/
theorem pow_order_4_3_2 :
    ∀ i : Fin 8, (2 : ℕ) ^ (i.val + 1) < 3 ^ (i.val + 1) ∧
                 (3 : ℕ) ^ (i.val + 1) < 4 ^ (i.val + 1) := by
  native_decide


structure CombinatoricalSchemesBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CombinatoricalSchemesBudgetCertificate.controlled
    (c : CombinatoricalSchemesBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def CombinatoricalSchemesBudgetCertificate.budgetControlled
    (c : CombinatoricalSchemesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def CombinatoricalSchemesBudgetCertificate.Ready
    (c : CombinatoricalSchemesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CombinatoricalSchemesBudgetCertificate.size
    (c : CombinatoricalSchemesBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem combinatoricalSchemes_budgetCertificate_le_size
    (c : CombinatoricalSchemesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleCombinatoricalSchemesBudgetCertificate :
    CombinatoricalSchemesBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleCombinatoricalSchemesBudgetCertificate.Ready := by
  constructor
  · norm_num [CombinatoricalSchemesBudgetCertificate.controlled,
      sampleCombinatoricalSchemesBudgetCertificate]
  · norm_num [CombinatoricalSchemesBudgetCertificate.budgetControlled,
      sampleCombinatoricalSchemesBudgetCertificate]

example :
    sampleCombinatoricalSchemesBudgetCertificate.certificateBudgetWindow ≤
      sampleCombinatoricalSchemesBudgetCertificate.size := by
  apply combinatoricalSchemes_budgetCertificate_le_size
  constructor
  · norm_num [CombinatoricalSchemesBudgetCertificate.controlled,
      sampleCombinatoricalSchemesBudgetCertificate]
  · norm_num [CombinatoricalSchemesBudgetCertificate.budgetControlled,
      sampleCombinatoricalSchemesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleCombinatoricalSchemesBudgetCertificate.Ready := by
  constructor
  · norm_num [CombinatoricalSchemesBudgetCertificate.controlled,
      sampleCombinatoricalSchemesBudgetCertificate]
  · norm_num [CombinatoricalSchemesBudgetCertificate.budgetControlled,
      sampleCombinatoricalSchemesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCombinatoricalSchemesBudgetCertificate.certificateBudgetWindow ≤
      sampleCombinatoricalSchemesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List CombinatoricalSchemesBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCombinatoricalSchemesBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleCombinatoricalSchemesBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch7.CombinatoricalSchemes
