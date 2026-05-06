import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Bridge between Mellin transfer and Tauberian windows.
-/

namespace AnalyticCombinatorics.Asymptotics.MellinTauberianBridge

/-- Finite Mellin prefix moment for sampled coefficient data. -/
def mellinPrefixQ (a : ℕ → ℚ) (s n : ℕ) : ℚ :=
  (List.range (n + 1)).foldl
    (fun total k => total + a k / ((k + 1 : ℚ) ^ s)) 0

/-- Ordinary summatory prefix used on the Tauberian side. -/
def summatoryPrefixQ (a : ℕ → ℚ) (n : ℕ) : ℚ :=
  (List.range (n + 1)).foldl (fun total k => total + a k) 0

/-- Finite bridge audit comparing Mellin and Tauberian sampled prefixes. -/
def mellinTauberianBridgeCheck
    (a : ℕ → ℚ) (s N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    mellinPrefixQ a s n ≤ summatoryPrefixQ a n

def MellinTauberianBridgeWindow
    (a : ℕ → ℚ) (s N : ℕ) : Prop :=
  mellinTauberianBridgeCheck a s N = true

theorem unit_mellinPrefix_samples :
    mellinPrefixQ (fun _ => 1) 2 0 = 1 ∧
    mellinPrefixQ (fun _ => 1) 2 1 = 5 / 4 ∧
    mellinPrefixQ (fun _ => 1) 2 2 = 49 / 36 := by
  unfold mellinPrefixQ
  native_decide

theorem unit_mellinTauberianBridgeWindow :
    MellinTauberianBridgeWindow (fun _ => 1) 2 24 := by
  unfold MellinTauberianBridgeWindow mellinTauberianBridgeCheck
    mellinPrefixQ summatoryPrefixQ
  native_decide

/-- Finite monotonicity audit for Tauberian summatory prefixes. -/
def summatoryMonotoneCheck (a : ℕ → ℚ) (N : ℕ) : Bool :=
  (List.range N).all fun n => summatoryPrefixQ a n ≤ summatoryPrefixQ a (n + 1)

theorem unit_summatoryMonotoneWindow :
    summatoryMonotoneCheck (fun _ => 1) 24 = true := by
  unfold summatoryMonotoneCheck summatoryPrefixQ
  native_decide

example : summatoryPrefixQ (fun _ => 1) 4 = 5 := by
  unfold summatoryPrefixQ
  native_decide

example :
    mellinTauberianBridgeCheck (fun _ => 1) 2 5 = true := by
  unfold mellinTauberianBridgeCheck mellinPrefixQ summatoryPrefixQ
  native_decide

structure MellinTauberianBridgeBudgetCertificate where
  mellinWindow : ℕ
  tauberianWindow : ℕ
  comparisonWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MellinTauberianBridgeBudgetCertificate.controlled
    (c : MellinTauberianBridgeBudgetCertificate) : Prop :=
  0 < c.mellinWindow ∧
    c.comparisonWindow ≤ c.mellinWindow + c.tauberianWindow + c.slack

def MellinTauberianBridgeBudgetCertificate.budgetControlled
    (c : MellinTauberianBridgeBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.mellinWindow + c.tauberianWindow + c.comparisonWindow + c.slack

def MellinTauberianBridgeBudgetCertificate.Ready
    (c : MellinTauberianBridgeBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def MellinTauberianBridgeBudgetCertificate.size
    (c : MellinTauberianBridgeBudgetCertificate) : ℕ :=
  c.mellinWindow + c.tauberianWindow + c.comparisonWindow + c.slack

theorem mellinTauberianBridge_budgetCertificate_le_size
    (c : MellinTauberianBridgeBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleMellinTauberianBridgeBudgetCertificate :
    MellinTauberianBridgeBudgetCertificate :=
  { mellinWindow := 5
    tauberianWindow := 6
    comparisonWindow := 10
    certificateBudgetWindow := 22
    slack := 1 }

example : sampleMellinTauberianBridgeBudgetCertificate.Ready := by
  constructor
  · norm_num [MellinTauberianBridgeBudgetCertificate.controlled,
      sampleMellinTauberianBridgeBudgetCertificate]
  · norm_num [MellinTauberianBridgeBudgetCertificate.budgetControlled,
      sampleMellinTauberianBridgeBudgetCertificate]

/-- Finite executable readiness audit for Mellin-Tauberian bridge certificates. -/
def mellinTauberianBridgeCertificateListReady
    (certs : List MellinTauberianBridgeBudgetCertificate) : Bool :=
  certs.all fun c =>
    0 < c.mellinWindow &&
      c.comparisonWindow ≤ c.mellinWindow + c.tauberianWindow + c.slack &&
        c.certificateBudgetWindow ≤
          c.mellinWindow + c.tauberianWindow + c.comparisonWindow + c.slack

theorem mellinTauberianBridgeCertificateList_readyWindow :
    mellinTauberianBridgeCertificateListReady
      [{ mellinWindow := 3, tauberianWindow := 4, comparisonWindow := 6,
         certificateBudgetWindow := 13, slack := 0 },
       { mellinWindow := 5, tauberianWindow := 6, comparisonWindow := 10,
         certificateBudgetWindow := 22, slack := 1 }] = true := by
  unfold mellinTauberianBridgeCertificateListReady
  native_decide

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleMellinTauberianBridgeBudgetCertificate.Ready := by
  constructor
  · norm_num [MellinTauberianBridgeBudgetCertificate.controlled,
      sampleMellinTauberianBridgeBudgetCertificate]
  · norm_num [MellinTauberianBridgeBudgetCertificate.budgetControlled,
      sampleMellinTauberianBridgeBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleMellinTauberianBridgeBudgetCertificate.certificateBudgetWindow ≤
      sampleMellinTauberianBridgeBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List MellinTauberianBridgeBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleMellinTauberianBridgeBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleMellinTauberianBridgeBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.MellinTauberianBridge
