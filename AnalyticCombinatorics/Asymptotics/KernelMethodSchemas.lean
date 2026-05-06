import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Kernel-method schema bookkeeping.

The module records finite kernel roots, boundary terms, and residual budgets
for functional equations.
-/

namespace AnalyticCombinatorics.Asymptotics.KernelMethodSchemas

structure KernelDatum where
  rootCount : ℕ
  boundaryTermBudget : ℕ
  residualBudget : ℕ
deriving DecidableEq, Repr

def hasKernelRoot (d : KernelDatum) : Prop :=
  0 < d.rootCount

def kernelResidualControlled (d : KernelDatum) : Prop :=
  d.residualBudget ≤ d.boundaryTermBudget + d.rootCount

def kernelMethodReady (d : KernelDatum) : Prop :=
  hasKernelRoot d ∧ kernelResidualControlled d

def kernelBudget (d : KernelDatum) : ℕ :=
  d.rootCount + d.boundaryTermBudget + d.residualBudget

theorem kernelMethodReady.root {d : KernelDatum}
    (h : kernelMethodReady d) :
    hasKernelRoot d ∧ kernelResidualControlled d ∧ d.residualBudget ≤ kernelBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold kernelBudget
  omega

theorem rootCount_le_kernelBudget (d : KernelDatum) :
    d.rootCount ≤ kernelBudget d := by
  unfold kernelBudget
  omega

def sampleKernelDatum : KernelDatum :=
  { rootCount := 2, boundaryTermBudget := 7, residualBudget := 3 }

example : kernelMethodReady sampleKernelDatum := by
  norm_num [kernelMethodReady, hasKernelRoot, kernelResidualControlled, sampleKernelDatum]

example : kernelBudget sampleKernelDatum = 12 := by
  native_decide

/-- Finite executable readiness audit for kernel-method data. -/
def kernelDatumListReady (data : List KernelDatum) : Bool :=
  data.all fun d =>
    0 < d.rootCount && d.residualBudget ≤ d.boundaryTermBudget + d.rootCount

theorem kernelDatumList_readyWindow :
    kernelDatumListReady
      [{ rootCount := 1, boundaryTermBudget := 4, residualBudget := 2 },
       { rootCount := 2, boundaryTermBudget := 7, residualBudget := 3 }] = true := by
  unfold kernelDatumListReady
  native_decide

structure KernelMethodWindow where
  rootCount : ℕ
  boundaryTermBudget : ℕ
  residualBudget : ℕ
  eliminationBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def KernelMethodWindow.residualControlled (w : KernelMethodWindow) : Prop :=
  w.residualBudget ≤ w.boundaryTermBudget + w.rootCount + w.slack

def KernelMethodWindow.eliminationControlled (w : KernelMethodWindow) : Prop :=
  w.eliminationBudget ≤ w.rootCount + w.boundaryTermBudget + w.residualBudget + w.slack

def kernelMethodWindowReady (w : KernelMethodWindow) : Prop :=
  0 < w.rootCount ∧
    w.residualControlled ∧
    w.eliminationControlled

def KernelMethodWindow.certificate (w : KernelMethodWindow) : ℕ :=
  w.rootCount + w.boundaryTermBudget + w.residualBudget + w.slack

theorem kernelMethod_eliminationBudget_le_certificate {w : KernelMethodWindow}
    (h : kernelMethodWindowReady w) :
    w.eliminationBudget ≤ w.certificate := by
  rcases h with ⟨_, _, helim⟩
  exact helim

def sampleKernelMethodWindow : KernelMethodWindow :=
  { rootCount := 2, boundaryTermBudget := 7, residualBudget := 3, eliminationBudget := 11,
    slack := 0 }

example : kernelMethodWindowReady sampleKernelMethodWindow := by
  norm_num [kernelMethodWindowReady, KernelMethodWindow.residualControlled,
    KernelMethodWindow.eliminationControlled, sampleKernelMethodWindow]

example : sampleKernelMethodWindow.certificate = 12 := by
  native_decide

structure KernelMethodCertificate where
  rootWindow : ℕ
  boundaryWindow : ℕ
  residualWindow : ℕ
  eliminationWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def KernelMethodCertificate.residualControlled
    (c : KernelMethodCertificate) : Prop :=
  c.residualWindow ≤ c.boundaryWindow + c.rootWindow + c.slack

def KernelMethodCertificate.eliminationControlled
    (c : KernelMethodCertificate) : Prop :=
  c.eliminationWindow ≤ c.rootWindow + c.boundaryWindow + c.residualWindow + c.slack

def kernelMethodCertificateReady
    (c : KernelMethodCertificate) : Prop :=
  0 < c.rootWindow ∧ c.residualControlled ∧ c.eliminationControlled

def KernelMethodCertificate.size
    (c : KernelMethodCertificate) : ℕ :=
  c.rootWindow + c.boundaryWindow + c.residualWindow + c.slack

theorem kernelMethod_eliminationWindow_le_size
    {c : KernelMethodCertificate}
    (h : kernelMethodCertificateReady c) :
    c.eliminationWindow ≤ c.size := by
  rcases h with ⟨_, _, helimination⟩
  exact helimination

def sampleKernelMethodCertificate : KernelMethodCertificate :=
  { rootWindow := 2, boundaryWindow := 7, residualWindow := 3,
    eliminationWindow := 11, slack := 0 }

example : kernelMethodCertificateReady sampleKernelMethodCertificate := by
  norm_num [kernelMethodCertificateReady,
    KernelMethodCertificate.residualControlled,
    KernelMethodCertificate.eliminationControlled,
    sampleKernelMethodCertificate]

example :
    sampleKernelMethodCertificate.eliminationWindow ≤
      sampleKernelMethodCertificate.size := by
  norm_num [KernelMethodCertificate.size, sampleKernelMethodCertificate]

/-- A refinement certificate with the kernel-elimination budget separated from size. -/
structure KernelMethodRefinementCertificate where
  rootWindow : ℕ
  boundaryWindow : ℕ
  residualWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def KernelMethodRefinementCertificate.residualControlled
    (cert : KernelMethodRefinementCertificate) : Prop :=
  0 < cert.rootWindow ∧
    cert.residualWindow ≤ cert.boundaryWindow + cert.rootWindow + cert.slack

def KernelMethodRefinementCertificate.budgetControlled
    (cert : KernelMethodRefinementCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.rootWindow + cert.boundaryWindow + cert.residualWindow + cert.slack

def kernelMethodRefinementReady
    (cert : KernelMethodRefinementCertificate) : Prop :=
  cert.residualControlled ∧ cert.budgetControlled

def KernelMethodRefinementCertificate.size
    (cert : KernelMethodRefinementCertificate) : ℕ :=
  cert.rootWindow + cert.boundaryWindow + cert.residualWindow + cert.slack

theorem kernelMethod_certificateBudgetWindow_le_size
    (cert : KernelMethodRefinementCertificate)
    (h : kernelMethodRefinementReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleKernelMethodRefinementCertificate :
    KernelMethodRefinementCertificate :=
  { rootWindow := 2, boundaryWindow := 7, residualWindow := 3,
    certificateBudgetWindow := 12, slack := 0 }

example :
    kernelMethodRefinementReady sampleKernelMethodRefinementCertificate := by
  norm_num [kernelMethodRefinementReady,
    KernelMethodRefinementCertificate.residualControlled,
    KernelMethodRefinementCertificate.budgetControlled,
    sampleKernelMethodRefinementCertificate]

example :
    sampleKernelMethodRefinementCertificate.certificateBudgetWindow ≤
      sampleKernelMethodRefinementCertificate.size := by
  apply kernelMethod_certificateBudgetWindow_le_size
  norm_num [kernelMethodRefinementReady,
    KernelMethodRefinementCertificate.residualControlled,
    KernelMethodRefinementCertificate.budgetControlled,
    sampleKernelMethodRefinementCertificate]


structure KernelMethodSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def KernelMethodSchemasBudgetCertificate.controlled
    (c : KernelMethodSchemasBudgetCertificate) : Prop :=
  0 < c.primaryWindow ∧ c.secondaryWindow ≤ c.primaryWindow + c.slack

def KernelMethodSchemasBudgetCertificate.budgetControlled
    (c : KernelMethodSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def KernelMethodSchemasBudgetCertificate.Ready
    (c : KernelMethodSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def KernelMethodSchemasBudgetCertificate.size
    (c : KernelMethodSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem kernelMethodSchemas_budgetCertificate_le_size
    (c : KernelMethodSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleKernelMethodSchemasBudgetCertificate :
    KernelMethodSchemasBudgetCertificate :=
  { primaryWindow := 5
    secondaryWindow := 6
    certificateBudgetWindow := 12
    slack := 1 }

example : sampleKernelMethodSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [KernelMethodSchemasBudgetCertificate.controlled,
      sampleKernelMethodSchemasBudgetCertificate]
  · norm_num [KernelMethodSchemasBudgetCertificate.budgetControlled,
      sampleKernelMethodSchemasBudgetCertificate]

example :
    sampleKernelMethodSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleKernelMethodSchemasBudgetCertificate.size := by
  apply kernelMethodSchemas_budgetCertificate_le_size
  constructor
  · norm_num [KernelMethodSchemasBudgetCertificate.controlled,
      sampleKernelMethodSchemasBudgetCertificate]
  · norm_num [KernelMethodSchemasBudgetCertificate.budgetControlled,
      sampleKernelMethodSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleKernelMethodSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [KernelMethodSchemasBudgetCertificate.controlled,
      sampleKernelMethodSchemasBudgetCertificate]
  · norm_num [KernelMethodSchemasBudgetCertificate.budgetControlled,
      sampleKernelMethodSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleKernelMethodSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleKernelMethodSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List KernelMethodSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleKernelMethodSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleKernelMethodSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.KernelMethodSchemas
