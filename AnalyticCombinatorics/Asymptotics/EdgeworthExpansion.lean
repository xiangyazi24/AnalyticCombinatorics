import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Edgeworth expansion
-/

namespace AnalyticCombinatorics.Asymptotics.EdgeworthExpansion

/-- Cumulant table over a finite order range. -/
def cumulantProxy (order scale : ℕ) : ℕ :=
  scale * order

theorem cumulantProxy_zero_order (scale : ℕ) :
    cumulantProxy 0 scale = 0 := by
  simp [cumulantProxy]

theorem cumulantProxy_pos {order scale : ℕ}
    (ho : 0 < order) (hs : 0 < scale) :
    0 < cumulantProxy order scale := by
  unfold cumulantProxy
  exact Nat.mul_pos hs ho

/-- Finite Hermite-like polynomial model for Edgeworth correction terms. -/
def edgeworthPolynomialProxy (cumulantOrder x : ℕ) : ℕ :=
  (x + 1) ^ cumulantOrder

theorem edgeworthPolynomialProxy_zero_order (x : ℕ) :
    edgeworthPolynomialProxy 0 x = 1 := by
  simp [edgeworthPolynomialProxy]

def edgeworthRemainderEnvelope (order sampleSize : ℕ) : ℕ :=
  (order + 1) * (sampleSize + 1)

theorem edgeworthRemainderEnvelope_pos (order sampleSize : ℕ) :
    0 < edgeworthRemainderEnvelope order sampleSize := by
  unfold edgeworthRemainderEnvelope
  exact Nat.mul_pos (Nat.succ_pos order) (Nat.succ_pos sampleSize)

def edgeworthEnvelopeCheck (order sampleSize bound : ℕ) : Bool :=
  edgeworthRemainderEnvelope order sampleSize ≤ bound

theorem edgeworthEnvelopeCheck_sample :
    edgeworthEnvelopeCheck 2 4 15 = true := by
  unfold edgeworthEnvelopeCheck edgeworthRemainderEnvelope
  native_decide

structure EdgeworthWindow where
  cumulantWindow : ℕ
  polynomialWindow : ℕ
  remainderWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def EdgeworthWindow.ready (w : EdgeworthWindow) : Prop :=
  0 < w.cumulantWindow ∧
    w.remainderWindow ≤ w.cumulantWindow + w.polynomialWindow + w.slack

def sampleEdgeworthWindow : EdgeworthWindow :=
  { cumulantWindow := 4, polynomialWindow := 3,
    remainderWindow := 7, slack := 0 }

example : sampleEdgeworthWindow.ready := by
  norm_num [EdgeworthWindow.ready, sampleEdgeworthWindow]

structure BudgetCertificate where
  cumulantWindow : ℕ
  remainderWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.cumulantWindow ∧ c.remainderWindow ≤ c.cumulantWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.cumulantWindow + c.remainderWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.cumulantWindow + c.remainderWindow + c.slack

def sampleBudgetCertificate : BudgetCertificate :=
  { cumulantWindow := 5, remainderWindow := 6,
    certificateBudgetWindow := 12, slack := 1 }

example : sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled, sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled, sampleBudgetCertificate]

theorem sampleBudgetCertificate_ready :
    sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled,
      sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled,
      sampleBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleBudgetCertificate.certificateBudgetWindow ≤
      sampleBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List BudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleBudgetCertificate
  native_decide

end AnalyticCombinatorics.Asymptotics.EdgeworthExpansion
