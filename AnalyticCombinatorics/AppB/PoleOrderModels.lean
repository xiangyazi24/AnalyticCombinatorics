import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite pole-order bookkeeping for meromorphic schemas.

The analytic part of a meromorphic transfer theorem can be separated from
the integer accounting of orders and principal-part sizes.
-/

namespace AnalyticCombinatorics.AppB.PoleOrderModels

structure PoleProfile where
  order : ℕ
  residueScale : ℕ
  analyticRemainder : ℕ
deriving DecidableEq, Repr

def simplePole (p : PoleProfile) : Prop :=
  p.order = 1

def principalPartBound (p : PoleProfile) : ℕ :=
  p.residueScale + p.analyticRemainder

def raiseOrder (p : PoleProfile) (extra : ℕ) : PoleProfile :=
  { p with order := p.order + extra }

theorem principalPartBound_mono {p q : PoleProfile}
    (hr : p.residueScale ≤ q.residueScale)
    (ha : p.analyticRemainder ≤ q.analyticRemainder) :
    principalPartBound p ≤ principalPartBound q := by
  unfold principalPartBound
  omega

theorem raiseOrder_positive {p : PoleProfile} {extra : ℕ}
    (h : 0 < p.order) :
    0 < (raiseOrder p extra).order := by
  change 0 < p.order + extra
  omega

def samplePole : PoleProfile :=
  { order := 1, residueScale := 5, analyticRemainder := 2 }

example : simplePole samplePole := by
  norm_num [simplePole, samplePole]

example : principalPartBound samplePole = 7 := by
  native_decide

example : (raiseOrder samplePole 3).order = 4 := by
  native_decide

structure PoleOrderWindow where
  orderWindow : ℕ
  residueWindow : ℕ
  remainderWindow : ℕ
  principalBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PoleOrderWindow.principalControlled (w : PoleOrderWindow) : Prop :=
  w.principalBudget ≤ w.residueWindow + w.remainderWindow + w.slack

def poleOrderWindowReady (w : PoleOrderWindow) : Prop :=
  0 < w.orderWindow ∧ w.principalControlled

def PoleOrderWindow.certificate (w : PoleOrderWindow) : ℕ :=
  w.orderWindow + w.residueWindow + w.remainderWindow + w.principalBudget + w.slack

theorem poleOrder_principalBudget_le_certificate (w : PoleOrderWindow) :
    w.principalBudget ≤ w.certificate := by
  unfold PoleOrderWindow.certificate
  omega

def samplePoleOrderWindow : PoleOrderWindow :=
  { orderWindow := 1, residueWindow := 5, remainderWindow := 2, principalBudget := 8, slack := 1 }

example : poleOrderWindowReady samplePoleOrderWindow := by
  norm_num [poleOrderWindowReady, PoleOrderWindow.principalControlled, samplePoleOrderWindow]


structure PoleOrderModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PoleOrderModelsBudgetCertificate.controlled
    (c : PoleOrderModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def PoleOrderModelsBudgetCertificate.budgetControlled
    (c : PoleOrderModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def PoleOrderModelsBudgetCertificate.Ready
    (c : PoleOrderModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PoleOrderModelsBudgetCertificate.size
    (c : PoleOrderModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem poleOrderModels_budgetCertificate_le_size
    (c : PoleOrderModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def samplePoleOrderModelsBudgetCertificate :
    PoleOrderModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    samplePoleOrderModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [PoleOrderModelsBudgetCertificate.controlled,
      samplePoleOrderModelsBudgetCertificate]
  · norm_num [PoleOrderModelsBudgetCertificate.budgetControlled,
      samplePoleOrderModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    samplePoleOrderModelsBudgetCertificate.certificateBudgetWindow ≤
      samplePoleOrderModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : samplePoleOrderModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [PoleOrderModelsBudgetCertificate.controlled,
      samplePoleOrderModelsBudgetCertificate]
  · norm_num [PoleOrderModelsBudgetCertificate.budgetControlled,
      samplePoleOrderModelsBudgetCertificate]

example :
    samplePoleOrderModelsBudgetCertificate.certificateBudgetWindow ≤
      samplePoleOrderModelsBudgetCertificate.size := by
  apply poleOrderModels_budgetCertificate_le_size
  constructor
  · norm_num [PoleOrderModelsBudgetCertificate.controlled,
      samplePoleOrderModelsBudgetCertificate]
  · norm_num [PoleOrderModelsBudgetCertificate.budgetControlled,
      samplePoleOrderModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List PoleOrderModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [samplePoleOrderModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady samplePoleOrderModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.PoleOrderModels
