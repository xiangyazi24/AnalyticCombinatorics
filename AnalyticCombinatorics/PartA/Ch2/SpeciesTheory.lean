import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartA.Ch2.SpeciesTheory


open scoped BigOperators

/-! Finite computational checks for Chapter II species and cycle-index examples.

All data are intentionally bounded.  The tables use `Fin` domains and the
statements below are closed finite propositions discharged by native
evaluation.
-/

def tableGet {n : ℕ} (A : Fin n → ℕ) (k : ℕ) : ℕ :=
  if h : k < n then A ⟨k, h⟩ else 0

def tableGet₂ {m n : ℕ} (A : Fin m → Fin n → ℕ) (i j : ℕ) : ℕ :=
  if hi : i < m then
    if hj : j < n then A ⟨i, hi⟩ ⟨j, hj⟩ else 0
  else 0

/-! ## Cycle-index coefficients for small symmetric groups -/

def cycleTypeSize (m : Fin 8 → ℕ) : ℕ :=
  ∑ i : Fin 8, (i.val + 1) * m i

def cycleIndexDenominator (m : Fin 8 → ℕ) : ℕ :=
  ∏ i : Fin 8, ((i.val + 1) ^ m i) * (m i).factorial

/-- `n!` times the coefficient of a cycle-index monomial. -/
def cycleIndexScaledCoeff (n : ℕ) (m : Fin 8 → ℕ) : ℕ :=
  if cycleTypeSize m = n then n.factorial / cycleIndexDenominator m else 0

def s4CycleTypes : Fin 5 → Fin 8 → ℕ :=
  ![
    ![4, 0, 0, 0, 0, 0, 0, 0],
    ![2, 1, 0, 0, 0, 0, 0, 0],
    ![0, 2, 0, 0, 0, 0, 0, 0],
    ![1, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0]
  ]

def s4CycleIndexDenominatorTable : Fin 5 → ℕ :=
  ![24, 4, 8, 3, 4]

def s4CycleClassSizeTable : Fin 5 → ℕ :=
  ![1, 6, 3, 8, 6]

theorem s4_cycle_index_denominators_checked :
    ∀ i : Fin 5,
      cycleIndexDenominator (s4CycleTypes i) = s4CycleIndexDenominatorTable i := by
  native_decide

theorem s4_cycle_index_scaled_coefficients_checked :
    ∀ i : Fin 5,
      cycleIndexScaledCoeff 4 (s4CycleTypes i) = s4CycleClassSizeTable i := by
  native_decide

theorem s4_cycle_index_coefficients_sum_to_factorial :
    (∑ i : Fin 5, cycleIndexScaledCoeff 4 (s4CycleTypes i)) = Nat.factorial 4 := by
  native_decide

/-! ## Small labelled species products and compositions -/

def atomSpeciesTable : Fin 9 → ℕ :=
  ![0, 1, 0, 0, 0, 0, 0, 0, 0]

def setSpeciesTable : Fin 9 → ℕ :=
  ![1, 1, 1, 1, 1, 1, 1, 1, 1]

def nonemptySetSpeciesTable : Fin 9 → ℕ :=
  ![0, 1, 1, 1, 1, 1, 1, 1, 1]

def speciesProduct (F G : Fin 9 → ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), Nat.choose n k * tableGet F k * tableGet G (n - k)

def atomTimesSetTable : Fin 9 → ℕ :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8]

theorem atom_times_set_species_product_checked :
    ∀ n : Fin 9, speciesProduct atomSpeciesTable setSpeciesTable n.val = atomTimesSetTable n := by
  native_decide

/-- Composition with the atomic species on the right preserves a counting table. -/
def composeWithAtomRight (F : Fin 9 → ℕ) (n : ℕ) : ℕ :=
  tableGet F n

theorem set_species_composed_with_atom_checked :
    ∀ n : Fin 9, composeWithAtomRight setSpeciesTable n.val = setSpeciesTable n := by
  native_decide

/-- Stirling numbers `S(n,k)` for `0 ≤ n,k ≤ 8`, padded by zeroes. -/
def stirlingSecondSmall : Fin 9 → Fin 9 → ℕ :=
  ![
    ![1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 1, 0, 0, 0, 0, 0, 0],
    ![0, 1, 3, 1, 0, 0, 0, 0, 0],
    ![0, 1, 7, 6, 1, 0, 0, 0, 0],
    ![0, 1, 15, 25, 10, 1, 0, 0, 0],
    ![0, 1, 31, 90, 65, 15, 1, 0, 0],
    ![0, 1, 63, 301, 350, 140, 21, 1, 0],
    ![0, 1, 127, 966, 1701, 1050, 266, 28, 1]
  ]

def setOfNonemptySetsComposition (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), tableGet₂ stirlingSecondSmall n k

def bellSmallTable : Fin 9 → ℕ :=
  ![1, 1, 2, 5, 15, 52, 203, 877, 4140]

theorem stirling_second_recurrence_small_checked :
    ∀ n : Fin 8, ∀ k : Fin 8,
      tableGet₂ stirlingSecondSmall (n.val + 1) (k.val + 1) =
        (k.val + 1) * tableGet₂ stirlingSecondSmall n.val (k.val + 1) +
          tableGet₂ stirlingSecondSmall n.val k.val := by
  native_decide

theorem set_of_nonempty_sets_composition_gives_bell_checked :
    ∀ n : Fin 9, setOfNonemptySetsComposition n.val = bellSmallTable n := by
  native_decide

/-! ## Burnside enumeration: necklaces and bracelets -/

def rotationBurnsideSum (colors n : ℕ) : ℕ :=
  ∑ shift ∈ Finset.range n, colors ^ Nat.gcd n shift

def necklaceBurnside (colors n : ℕ) : ℕ :=
  if n = 0 then 1 else rotationBurnsideSum colors n / n

def reflectionBurnsideSum (colors n : ℕ) : ℕ :=
  if n = 0 then 0
  else if n % 2 = 1 then n * colors ^ ((n + 1) / 2)
  else (n / 2) * colors ^ (n / 2 + 1) + (n / 2) * colors ^ (n / 2)

def braceletBurnside (colors n : ℕ) : ℕ :=
  if n = 0 then 1 else (rotationBurnsideSum colors n + reflectionBurnsideSum colors n) / (2 * n)

def binaryNecklaceTable : Fin 9 → ℕ :=
  ![1, 2, 3, 4, 6, 8, 14, 20, 36]

def binaryBraceletTable : Fin 9 → ℕ :=
  ![1, 2, 3, 4, 6, 8, 13, 18, 30]

theorem binary_necklace_burnside_checked :
    ∀ n : Fin 9, necklaceBurnside 2 n.val = binaryNecklaceTable n := by
  native_decide

theorem binary_bracelet_burnside_checked :
    ∀ n : Fin 9, braceletBurnside 2 n.val = binaryBraceletTable n := by
  native_decide

/-! ## Redfield-Polya inventories by black-bead count -/

def rotationFixedBinaryByWeight (n shift weight : ℕ) : ℕ :=
  if n = 0 then
    if weight = 0 then 1 else 0
  else
    let cycles := Nat.gcd n shift
    let cycleLength := n / cycles
    if cycleLength = 0 then 0
    else if weight % cycleLength = 0 then Nat.choose cycles (weight / cycleLength)
    else 0

def binaryNecklaceInventory (n weight : ℕ) : ℕ :=
  if n = 0 then
    if weight = 0 then 1 else 0
  else
    (∑ shift ∈ Finset.range n, rotationFixedBinaryByWeight n shift weight) / n

def binaryNecklaceInventory4 : Fin 5 → ℕ :=
  ![1, 1, 2, 1, 1]

def binaryNecklaceInventory5 : Fin 6 → ℕ :=
  ![1, 1, 2, 2, 1, 1]

theorem redfield_polya_binary_necklace_inventory_four_checked :
    ∀ weight : Fin 5,
      binaryNecklaceInventory 4 weight.val = binaryNecklaceInventory4 weight := by
  native_decide

theorem redfield_polya_binary_necklace_inventory_five_checked :
    ∀ weight : Fin 6,
      binaryNecklaceInventory 5 weight.val = binaryNecklaceInventory5 weight := by
  native_decide



structure SpeciesTheoryBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SpeciesTheoryBudgetCertificate.controlled
    (c : SpeciesTheoryBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def SpeciesTheoryBudgetCertificate.budgetControlled
    (c : SpeciesTheoryBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def SpeciesTheoryBudgetCertificate.Ready
    (c : SpeciesTheoryBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SpeciesTheoryBudgetCertificate.size
    (c : SpeciesTheoryBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem speciesTheory_budgetCertificate_le_size
    (c : SpeciesTheoryBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSpeciesTheoryBudgetCertificate :
    SpeciesTheoryBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleSpeciesTheoryBudgetCertificate.Ready := by
  constructor
  · norm_num [SpeciesTheoryBudgetCertificate.controlled,
      sampleSpeciesTheoryBudgetCertificate]
  · norm_num [SpeciesTheoryBudgetCertificate.budgetControlled,
      sampleSpeciesTheoryBudgetCertificate]

example :
    sampleSpeciesTheoryBudgetCertificate.certificateBudgetWindow ≤
      sampleSpeciesTheoryBudgetCertificate.size := by
  apply speciesTheory_budgetCertificate_le_size
  constructor
  · norm_num [SpeciesTheoryBudgetCertificate.controlled,
      sampleSpeciesTheoryBudgetCertificate]
  · norm_num [SpeciesTheoryBudgetCertificate.budgetControlled,
      sampleSpeciesTheoryBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleSpeciesTheoryBudgetCertificate.Ready := by
  constructor
  · norm_num [SpeciesTheoryBudgetCertificate.controlled,
      sampleSpeciesTheoryBudgetCertificate]
  · norm_num [SpeciesTheoryBudgetCertificate.budgetControlled,
      sampleSpeciesTheoryBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSpeciesTheoryBudgetCertificate.certificateBudgetWindow ≤
      sampleSpeciesTheoryBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List SpeciesTheoryBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSpeciesTheoryBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleSpeciesTheoryBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch2.SpeciesTheory
