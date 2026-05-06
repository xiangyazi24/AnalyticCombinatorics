import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
de Bruijn conjugates.
-/

namespace AnalyticCombinatorics.Asymptotics.DeBruijnConjugates

/-- Finite paired-product audit for de Bruijn conjugate samples. -/
def conjugateProductWindowQ
    (L M : ℕ → ℚ) (lower upper : ℚ) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    lower ≤ L n * M n ∧ L n * M n ≤ upper

def unitScaleQ (_ : ℕ) : ℚ :=
  1

def linearScaleQ (n : ℕ) : ℚ :=
  n + 1

def reciprocalLinearScaleQ (n : ℕ) : ℚ :=
  1 / (n + 1 : ℚ)

/-- Finite statement form for paired de Bruijn conjugate samples. -/
def DeBruijnConjugateWindow
    (L M : ℕ → ℚ) (N : ℕ) : Prop :=
  conjugateProductWindowQ L M (1 / 2) 2 N = true

theorem unit_deBruijnConjugateWindow :
    DeBruijnConjugateWindow unitScaleQ unitScaleQ 32 := by
  unfold DeBruijnConjugateWindow conjugateProductWindowQ unitScaleQ
  native_decide

theorem linear_reciprocal_deBruijnConjugateWindow :
    DeBruijnConjugateWindow linearScaleQ reciprocalLinearScaleQ 32 := by
  unfold DeBruijnConjugateWindow conjugateProductWindowQ linearScaleQ
    reciprocalLinearScaleQ
  native_decide

/-- Finite exact-product audit for paired de Bruijn conjugate samples. -/
def conjugateProductExactCheck (L M : ℕ → ℚ) (target : ℚ) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => L n * M n = target

theorem linear_reciprocal_exactProductWindow :
    conjugateProductExactCheck linearScaleQ reciprocalLinearScaleQ 1 24 = true := by
  unfold conjugateProductExactCheck linearScaleQ reciprocalLinearScaleQ
  native_decide

example : linearScaleQ 4 * reciprocalLinearScaleQ 4 = 1 := by
  unfold linearScaleQ reciprocalLinearScaleQ
  native_decide

example :
    conjugateProductWindowQ
      linearScaleQ reciprocalLinearScaleQ (1 / 2) 2 8 = true := by
  unfold conjugateProductWindowQ linearScaleQ reciprocalLinearScaleQ
  native_decide

structure DeBruijnConjugatesBudgetCertificate where
  scaleWindow : ℕ
  conjugateWindow : ℕ
  inversionWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DeBruijnConjugatesBudgetCertificate.controlled
    (c : DeBruijnConjugatesBudgetCertificate) : Prop :=
  0 < c.scaleWindow ∧
    c.inversionWindow ≤ c.scaleWindow + c.conjugateWindow + c.slack

def DeBruijnConjugatesBudgetCertificate.budgetControlled
    (c : DeBruijnConjugatesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.scaleWindow + c.conjugateWindow + c.inversionWindow + c.slack

def DeBruijnConjugatesBudgetCertificate.Ready
    (c : DeBruijnConjugatesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def DeBruijnConjugatesBudgetCertificate.size
    (c : DeBruijnConjugatesBudgetCertificate) : ℕ :=
  c.scaleWindow + c.conjugateWindow + c.inversionWindow + c.slack

theorem deBruijnConjugates_budgetCertificate_le_size
    (c : DeBruijnConjugatesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleDeBruijnConjugatesBudgetCertificate :
    DeBruijnConjugatesBudgetCertificate :=
  { scaleWindow := 5
    conjugateWindow := 6
    inversionWindow := 10
    certificateBudgetWindow := 22
    slack := 1 }

/-- Finite executable readiness audit for de Bruijn conjugate budget certificates. -/
def deBruijnConjugatesListReady
    (certs : List DeBruijnConjugatesBudgetCertificate) : Bool :=
  certs.all fun c =>
    0 < c.scaleWindow &&
      c.inversionWindow ≤ c.scaleWindow + c.conjugateWindow + c.slack &&
        c.certificateBudgetWindow ≤
          c.scaleWindow + c.conjugateWindow + c.inversionWindow + c.slack

theorem deBruijnConjugatesList_readyWindow :
    deBruijnConjugatesListReady
      [{ scaleWindow := 3, conjugateWindow := 4, inversionWindow := 6,
         certificateBudgetWindow := 13, slack := 0 },
       { scaleWindow := 5, conjugateWindow := 6, inversionWindow := 10,
         certificateBudgetWindow := 22, slack := 1 }] = true := by
  unfold deBruijnConjugatesListReady
  native_decide

example : sampleDeBruijnConjugatesBudgetCertificate.Ready := by
  constructor
  · norm_num [DeBruijnConjugatesBudgetCertificate.controlled,
      sampleDeBruijnConjugatesBudgetCertificate]
  · norm_num [DeBruijnConjugatesBudgetCertificate.budgetControlled,
      sampleDeBruijnConjugatesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleDeBruijnConjugatesBudgetCertificate.Ready := by
  constructor
  · norm_num [DeBruijnConjugatesBudgetCertificate.controlled,
      sampleDeBruijnConjugatesBudgetCertificate]
  · norm_num [DeBruijnConjugatesBudgetCertificate.budgetControlled,
      sampleDeBruijnConjugatesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleDeBruijnConjugatesBudgetCertificate.certificateBudgetWindow ≤
      sampleDeBruijnConjugatesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List DeBruijnConjugatesBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleDeBruijnConjugatesBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleDeBruijnConjugatesBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.DeBruijnConjugates
