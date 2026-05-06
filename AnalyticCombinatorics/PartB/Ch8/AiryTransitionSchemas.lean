import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Airy-type transition bookkeeping for coalescing saddle points.

The finite schemas record the algebraic side of the cubic-saddle
normalization: vanishing quadratic term, nonzero cubic term, and scale.
-/

namespace AnalyticCombinatorics.PartB.Ch8.AiryTransitionSchemas

structure CubicSaddleProfile where
  quadraticTerm : ℕ
  cubicTerm : ℕ
  scale : ℕ
deriving DecidableEq, Repr

def cubicNondegenerate (p : CubicSaddleProfile) : Prop :=
  p.quadraticTerm = 0 ∧ 0 < p.cubicTerm ∧ 0 < p.scale

def rescaledIndex (scale offset n : ℕ) : ℕ :=
  scale * n + offset

theorem cubicNondegenerate.scale_pos {p : CubicSaddleProfile}
    (h : cubicNondegenerate p) :
    0 < p.scale := h.2.2

theorem rescaledIndex_succ (scale offset n : ℕ) :
    rescaledIndex scale offset (n + 1) =
      rescaledIndex scale offset n + scale := by
  unfold rescaledIndex
  rw [Nat.mul_succ]
  omega

def sampleCubic : CubicSaddleProfile :=
  { quadraticTerm := 0, cubicTerm := 3, scale := 5 }

example : cubicNondegenerate sampleCubic := by
  norm_num [cubicNondegenerate, sampleCubic]

example : rescaledIndex 5 2 4 = 22 := by
  native_decide

structure AiryTransitionWindow where
  cubicScale : ℕ
  linearDrift : ℕ
  transitionWidth : ℕ
  errorSlack : ℕ
deriving DecidableEq, Repr

def AiryTransitionWindow.scaleReady (w : AiryTransitionWindow) : Prop :=
  0 < w.cubicScale

def AiryTransitionWindow.widthControlled (w : AiryTransitionWindow) : Prop :=
  w.transitionWidth ≤ w.cubicScale + w.linearDrift + w.errorSlack

def AiryTransitionWindow.ready (w : AiryTransitionWindow) : Prop :=
  w.scaleReady ∧ w.widthControlled

def AiryTransitionWindow.certificate (w : AiryTransitionWindow) : ℕ :=
  w.cubicScale + w.linearDrift + w.transitionWidth + w.errorSlack

theorem transitionWidth_le_certificate (w : AiryTransitionWindow) :
    w.transitionWidth ≤ w.certificate := by
  unfold AiryTransitionWindow.certificate
  omega

def sampleAiryTransitionWindow : AiryTransitionWindow :=
  { cubicScale := 5, linearDrift := 2, transitionWidth := 6, errorSlack := 0 }

example : sampleAiryTransitionWindow.ready := by
  norm_num [sampleAiryTransitionWindow, AiryTransitionWindow.ready,
    AiryTransitionWindow.scaleReady, AiryTransitionWindow.widthControlled]


structure AiryTransitionSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AiryTransitionSchemasBudgetCertificate.controlled
    (c : AiryTransitionSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AiryTransitionSchemasBudgetCertificate.budgetControlled
    (c : AiryTransitionSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AiryTransitionSchemasBudgetCertificate.Ready
    (c : AiryTransitionSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AiryTransitionSchemasBudgetCertificate.size
    (c : AiryTransitionSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem airyTransitionSchemas_budgetCertificate_le_size
    (c : AiryTransitionSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAiryTransitionSchemasBudgetCertificate :
    AiryTransitionSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAiryTransitionSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [AiryTransitionSchemasBudgetCertificate.controlled,
      sampleAiryTransitionSchemasBudgetCertificate]
  · norm_num [AiryTransitionSchemasBudgetCertificate.budgetControlled,
      sampleAiryTransitionSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAiryTransitionSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleAiryTransitionSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAiryTransitionSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [AiryTransitionSchemasBudgetCertificate.controlled,
      sampleAiryTransitionSchemasBudgetCertificate]
  · norm_num [AiryTransitionSchemasBudgetCertificate.budgetControlled,
      sampleAiryTransitionSchemasBudgetCertificate]

example :
    sampleAiryTransitionSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleAiryTransitionSchemasBudgetCertificate.size := by
  apply airyTransitionSchemas_budgetCertificate_le_size
  constructor
  · norm_num [AiryTransitionSchemasBudgetCertificate.controlled,
      sampleAiryTransitionSchemasBudgetCertificate]
  · norm_num [AiryTransitionSchemasBudgetCertificate.budgetControlled,
      sampleAiryTransitionSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List AiryTransitionSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAiryTransitionSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAiryTransitionSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch8.AiryTransitionSchemas
