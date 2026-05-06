import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Sectorial domain models.

The finite abstraction tracks aperture, radial depth, and boundary slack
for sectorial analytic domains.
-/

namespace AnalyticCombinatorics.AppB.SectorialDomainModels

structure SectorialDomainData where
  aperture : ℕ
  radialDepth : ℕ
  boundarySlack : ℕ
deriving DecidableEq, Repr

def positiveAperture (d : SectorialDomainData) : Prop :=
  0 < d.aperture

def depthControlled (d : SectorialDomainData) : Prop :=
  d.radialDepth ≤ d.aperture + d.boundarySlack

def sectorialDomainReady (d : SectorialDomainData) : Prop :=
  positiveAperture d ∧ depthControlled d

def sectorialDomainBudget (d : SectorialDomainData) : ℕ :=
  d.aperture + d.radialDepth + d.boundarySlack

theorem sectorialDomainReady.aperture {d : SectorialDomainData}
    (h : sectorialDomainReady d) :
    positiveAperture d ∧ depthControlled d ∧
      d.radialDepth ≤ sectorialDomainBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold sectorialDomainBudget
  omega

theorem radialDepth_le_sectorialBudget (d : SectorialDomainData) :
    d.radialDepth ≤ sectorialDomainBudget d := by
  unfold sectorialDomainBudget
  omega

def sampleSectorialDomainData : SectorialDomainData :=
  { aperture := 5, radialDepth := 8, boundarySlack := 4 }

example : sectorialDomainReady sampleSectorialDomainData := by
  norm_num [sectorialDomainReady, positiveAperture]
  norm_num [depthControlled, sampleSectorialDomainData]

example : sectorialDomainBudget sampleSectorialDomainData = 17 := by
  native_decide

/-- Finite executable readiness audit for sectorial domains. -/
def sectorialDomainListReady (windows : List SectorialDomainData) : Bool :=
  windows.all fun d =>
    0 < d.aperture && d.radialDepth ≤ d.aperture + d.boundarySlack

theorem sectorialDomainList_readyWindow :
    sectorialDomainListReady
      [{ aperture := 3, radialDepth := 4, boundarySlack := 1 },
       { aperture := 5, radialDepth := 8, boundarySlack := 4 }] = true := by
  unfold sectorialDomainListReady
  native_decide


structure SectorialDomainModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SectorialDomainModelsBudgetCertificate.controlled
    (c : SectorialDomainModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def SectorialDomainModelsBudgetCertificate.budgetControlled
    (c : SectorialDomainModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def SectorialDomainModelsBudgetCertificate.Ready
    (c : SectorialDomainModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SectorialDomainModelsBudgetCertificate.size
    (c : SectorialDomainModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem sectorialDomainModels_budgetCertificate_le_size
    (c : SectorialDomainModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSectorialDomainModelsBudgetCertificate :
    SectorialDomainModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleSectorialDomainModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [SectorialDomainModelsBudgetCertificate.controlled,
      sampleSectorialDomainModelsBudgetCertificate]
  · norm_num [SectorialDomainModelsBudgetCertificate.budgetControlled,
      sampleSectorialDomainModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSectorialDomainModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleSectorialDomainModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleSectorialDomainModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [SectorialDomainModelsBudgetCertificate.controlled,
      sampleSectorialDomainModelsBudgetCertificate]
  · norm_num [SectorialDomainModelsBudgetCertificate.budgetControlled,
      sampleSectorialDomainModelsBudgetCertificate]

example :
    sampleSectorialDomainModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleSectorialDomainModelsBudgetCertificate.size := by
  apply sectorialDomainModels_budgetCertificate_le_size
  constructor
  · norm_num [SectorialDomainModelsBudgetCertificate.controlled,
      sampleSectorialDomainModelsBudgetCertificate]
  · norm_num [SectorialDomainModelsBudgetCertificate.budgetControlled,
      sampleSectorialDomainModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List SectorialDomainModelsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSectorialDomainModelsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleSectorialDomainModelsBudgetCertificate
  native_decide
end AnalyticCombinatorics.AppB.SectorialDomainModels
