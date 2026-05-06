import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform saddle-contour bookkeeping.

The file records finite width and descent budgets used before analytic
estimates on a family of saddle contours.
-/

namespace AnalyticCombinatorics.Asymptotics.UniformSaddleContours

structure SaddleContourData where
  contourWidth : ℕ
  descentBudget : ℕ
  tailBudget : ℕ
deriving DecidableEq, Repr

def positiveContourWidth (d : SaddleContourData) : Prop :=
  0 < d.contourWidth

def descentDominatesTail (d : SaddleContourData) : Prop :=
  d.tailBudget ≤ d.descentBudget

def uniformContourReady (d : SaddleContourData) : Prop :=
  positiveContourWidth d ∧ descentDominatesTail d

def totalContourBudget (d : SaddleContourData) : ℕ :=
  d.contourWidth + d.descentBudget + d.tailBudget

theorem uniformContourReady.width {d : SaddleContourData}
    (h : uniformContourReady d) :
    positiveContourWidth d ∧ descentDominatesTail d ∧ d.tailBudget ≤ totalContourBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold totalContourBudget
  omega

theorem contourWidth_le_total (d : SaddleContourData) :
    d.contourWidth ≤ totalContourBudget d := by
  unfold totalContourBudget
  omega

def sampleContour : SaddleContourData :=
  { contourWidth := 4, descentBudget := 9, tailBudget := 3 }

example : uniformContourReady sampleContour := by
  norm_num [uniformContourReady, positiveContourWidth, descentDominatesTail, sampleContour]

example : totalContourBudget sampleContour = 16 := by
  native_decide

/-- Finite executable readiness audit for saddle contour data. -/
def saddleContourDataListReady (data : List SaddleContourData) : Bool :=
  data.all fun d => 0 < d.contourWidth && d.tailBudget ≤ d.descentBudget

theorem saddleContourDataList_readyWindow :
    saddleContourDataListReady
      [{ contourWidth := 4, descentBudget := 9, tailBudget := 3 },
       { contourWidth := 5, descentBudget := 8, tailBudget := 8 }] = true := by
  unfold saddleContourDataListReady
  native_decide

structure UniformSaddleWindow where
  contourWidth : ℕ
  descentBudget : ℕ
  tailBudget : ℕ
  saddleBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformSaddleWindow.tailControlled (w : UniformSaddleWindow) : Prop :=
  w.tailBudget ≤ w.descentBudget + w.slack

def UniformSaddleWindow.saddleControlled (w : UniformSaddleWindow) : Prop :=
  w.saddleBudget ≤ w.contourWidth + w.descentBudget + w.tailBudget + w.slack

def uniformSaddleWindowReady (w : UniformSaddleWindow) : Prop :=
  0 < w.contourWidth ∧
    w.tailControlled ∧
    w.saddleControlled

def UniformSaddleWindow.certificate (w : UniformSaddleWindow) : ℕ :=
  w.contourWidth + w.descentBudget + w.tailBudget + w.slack

theorem uniformSaddle_saddleBudget_le_certificate {w : UniformSaddleWindow}
    (h : uniformSaddleWindowReady w) :
    w.saddleBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hsaddle⟩
  exact hsaddle

def sampleUniformSaddleWindow : UniformSaddleWindow :=
  { contourWidth := 4, descentBudget := 9, tailBudget := 3, saddleBudget := 15, slack := 0 }

example : uniformSaddleWindowReady sampleUniformSaddleWindow := by
  norm_num [uniformSaddleWindowReady, UniformSaddleWindow.tailControlled,
    UniformSaddleWindow.saddleControlled, sampleUniformSaddleWindow]

example : sampleUniformSaddleWindow.certificate = 16 := by
  native_decide

/-- A refinement certificate for uniform saddle contour windows. -/
structure UniformSaddleContourCertificate where
  contourWidthWindow : ℕ
  descentBudgetWindow : ℕ
  tailBudgetWindow : ℕ
  saddleBudgetWindow : ℕ
  slack : ℕ

/-- Tail and saddle budgets are controlled by descent and contour width. -/
def uniformSaddleContourCertificateControlled
    (w : UniformSaddleContourCertificate) : Prop :=
  0 < w.contourWidthWindow ∧
    w.tailBudgetWindow ≤ w.descentBudgetWindow + w.slack ∧
      w.saddleBudgetWindow ≤
        w.contourWidthWindow + w.descentBudgetWindow + w.tailBudgetWindow + w.slack

/-- Readiness for a uniform saddle contour certificate. -/
def uniformSaddleContourCertificateReady
    (w : UniformSaddleContourCertificate) : Prop :=
  uniformSaddleContourCertificateControlled w ∧
    w.saddleBudgetWindow ≤
      w.contourWidthWindow + w.descentBudgetWindow + w.tailBudgetWindow +
        w.saddleBudgetWindow + w.slack

/-- Total size of a uniform saddle contour certificate. -/
def uniformSaddleContourCertificateSize
    (w : UniformSaddleContourCertificate) : ℕ :=
  w.contourWidthWindow + w.descentBudgetWindow + w.tailBudgetWindow +
    w.saddleBudgetWindow + w.slack

theorem uniformSaddleContourCertificate_budget_le_size
    (w : UniformSaddleContourCertificate)
    (h : uniformSaddleContourCertificateReady w) :
    w.saddleBudgetWindow ≤ uniformSaddleContourCertificateSize w := by
  rcases h with ⟨_, hbudget⟩
  unfold uniformSaddleContourCertificateSize
  omega

def sampleUniformSaddleContourCertificate :
    UniformSaddleContourCertificate where
  contourWidthWindow := 4
  descentBudgetWindow := 9
  tailBudgetWindow := 3
  saddleBudgetWindow := 15
  slack := 0

example :
    uniformSaddleContourCertificateReady
      sampleUniformSaddleContourCertificate := by
  norm_num [uniformSaddleContourCertificateReady,
    uniformSaddleContourCertificateControlled,
    sampleUniformSaddleContourCertificate]

example :
    sampleUniformSaddleContourCertificate.saddleBudgetWindow ≤
      uniformSaddleContourCertificateSize
        sampleUniformSaddleContourCertificate := by
  apply uniformSaddleContourCertificate_budget_le_size
  norm_num [uniformSaddleContourCertificateReady,
    uniformSaddleContourCertificateControlled,
    sampleUniformSaddleContourCertificate]

/-- A refinement certificate with the uniform-saddle budget separated from size. -/
structure UniformSaddleContourRefinementCertificate where
  contourWidthWindow : ℕ
  descentBudgetWindow : ℕ
  tailBudgetWindow : ℕ
  saddleBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformSaddleContourRefinementCertificate.contourControlled
    (cert : UniformSaddleContourRefinementCertificate) : Prop :=
  0 < cert.contourWidthWindow ∧
    cert.tailBudgetWindow ≤ cert.descentBudgetWindow + cert.slack ∧
      cert.saddleBudgetWindow ≤
        cert.contourWidthWindow + cert.descentBudgetWindow + cert.tailBudgetWindow + cert.slack

def UniformSaddleContourRefinementCertificate.budgetControlled
    (cert : UniformSaddleContourRefinementCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.contourWidthWindow + cert.descentBudgetWindow + cert.tailBudgetWindow +
      cert.saddleBudgetWindow + cert.slack

def uniformSaddleContourRefinementReady
    (cert : UniformSaddleContourRefinementCertificate) : Prop :=
  cert.contourControlled ∧ cert.budgetControlled

def UniformSaddleContourRefinementCertificate.size
    (cert : UniformSaddleContourRefinementCertificate) : ℕ :=
  cert.contourWidthWindow + cert.descentBudgetWindow + cert.tailBudgetWindow +
    cert.saddleBudgetWindow + cert.slack

theorem uniformSaddleContour_certificateBudgetWindow_le_size
    (cert : UniformSaddleContourRefinementCertificate)
    (h : uniformSaddleContourRefinementReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformSaddleContourRefinementCertificate :
    UniformSaddleContourRefinementCertificate :=
  { contourWidthWindow := 4, descentBudgetWindow := 9, tailBudgetWindow := 3,
    saddleBudgetWindow := 15, certificateBudgetWindow := 31, slack := 0 }

example :
    uniformSaddleContourRefinementReady
      sampleUniformSaddleContourRefinementCertificate := by
  norm_num [uniformSaddleContourRefinementReady,
    UniformSaddleContourRefinementCertificate.contourControlled,
    UniformSaddleContourRefinementCertificate.budgetControlled,
    sampleUniformSaddleContourRefinementCertificate]

example :
    sampleUniformSaddleContourRefinementCertificate.certificateBudgetWindow ≤
      sampleUniformSaddleContourRefinementCertificate.size := by
  apply uniformSaddleContour_certificateBudgetWindow_le_size
  norm_num [uniformSaddleContourRefinementReady,
    UniformSaddleContourRefinementCertificate.contourControlled,
    UniformSaddleContourRefinementCertificate.budgetControlled,
    sampleUniformSaddleContourRefinementCertificate]


structure UniformSaddleContoursBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformSaddleContoursBudgetCertificate.controlled
    (c : UniformSaddleContoursBudgetCertificate) : Prop :=
  0 < c.primaryWindow ∧ c.secondaryWindow ≤ c.primaryWindow + c.slack

def UniformSaddleContoursBudgetCertificate.budgetControlled
    (c : UniformSaddleContoursBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def UniformSaddleContoursBudgetCertificate.Ready
    (c : UniformSaddleContoursBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UniformSaddleContoursBudgetCertificate.size
    (c : UniformSaddleContoursBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem uniformSaddleContours_budgetCertificate_le_size
    (c : UniformSaddleContoursBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformSaddleContoursBudgetCertificate :
    UniformSaddleContoursBudgetCertificate :=
  { primaryWindow := 5
    secondaryWindow := 6
    certificateBudgetWindow := 12
    slack := 1 }

example : sampleUniformSaddleContoursBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformSaddleContoursBudgetCertificate.controlled,
      sampleUniformSaddleContoursBudgetCertificate]
  · norm_num [UniformSaddleContoursBudgetCertificate.budgetControlled,
      sampleUniformSaddleContoursBudgetCertificate]

example :
    sampleUniformSaddleContoursBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformSaddleContoursBudgetCertificate.size := by
  apply uniformSaddleContours_budgetCertificate_le_size
  constructor
  · norm_num [UniformSaddleContoursBudgetCertificate.controlled,
      sampleUniformSaddleContoursBudgetCertificate]
  · norm_num [UniformSaddleContoursBudgetCertificate.budgetControlled,
      sampleUniformSaddleContoursBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleUniformSaddleContoursBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformSaddleContoursBudgetCertificate.controlled,
      sampleUniformSaddleContoursBudgetCertificate]
  · norm_num [UniformSaddleContoursBudgetCertificate.budgetControlled,
      sampleUniformSaddleContoursBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformSaddleContoursBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformSaddleContoursBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List UniformSaddleContoursBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformSaddleContoursBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleUniformSaddleContoursBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.UniformSaddleContours
