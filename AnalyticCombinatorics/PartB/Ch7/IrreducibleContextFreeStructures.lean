import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Irreducible context-free structures.

Finite grammar-window bookkeeping for irreducible context-free schemas.
-/

namespace AnalyticCombinatorics.PartB.Ch7.IrreducibleContextFreeStructures

/-- Finite grammar descriptor for an irreducibility audit. -/
structure GrammarDependencyWindow where
  nonterminals : ℕ
  reachablePairs : ℕ
  productions : ℕ
deriving DecidableEq, Repr

def GrammarDependencyWindow.irreducible (g : GrammarDependencyWindow) : Prop :=
  0 < g.nonterminals ∧ g.nonterminals * g.nonterminals ≤ g.reachablePairs + g.productions

def grammarIrreducibleBool (g : GrammarDependencyWindow) : Bool :=
  decide (0 < g.nonterminals) &&
    decide (g.nonterminals * g.nonterminals ≤ g.reachablePairs + g.productions)

def sampleIrreducibleGrammar : GrammarDependencyWindow :=
  { nonterminals := 2, reachablePairs := 4, productions := 1 }

theorem sampleIrreducibleGrammar_window :
    sampleIrreducibleGrammar.irreducible ∧
      grammarIrreducibleBool sampleIrreducibleGrammar = true := by
  constructor
  · norm_num [GrammarDependencyWindow.irreducible, sampleIrreducibleGrammar]
  · unfold grammarIrreducibleBool sampleIrreducibleGrammar
    native_decide

structure IrreducibleContextFreeWindow where
  nonterminalWindow : ℕ
  productionWindow : ℕ
  irreducibilityWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def irreducibleContextFreeReady
    (w : IrreducibleContextFreeWindow) : Prop :=
  0 < w.nonterminalWindow ∧
    w.irreducibilityWindow ≤
      w.nonterminalWindow + w.productionWindow + w.slack

def irreducibleContextFreeBudget
    (w : IrreducibleContextFreeWindow) : ℕ :=
  w.nonterminalWindow + w.productionWindow +
    w.irreducibilityWindow + w.slack

theorem irreducibilityWindow_le_contextFreeBudget
    (w : IrreducibleContextFreeWindow) :
    w.irreducibilityWindow ≤ irreducibleContextFreeBudget w := by
  unfold irreducibleContextFreeBudget
  omega

def sampleIrreducibleContextFreeWindow : IrreducibleContextFreeWindow :=
  { nonterminalWindow := 4
    productionWindow := 7
    irreducibilityWindow := 10
    slack := 1 }

example : irreducibleContextFreeReady sampleIrreducibleContextFreeWindow := by
  norm_num [irreducibleContextFreeReady, sampleIrreducibleContextFreeWindow]

structure IrreducibleContextFreeStructuresBudgetCertificate where
  nonterminalWindow : ℕ
  productionWindow : ℕ
  irreducibilityWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def IrreducibleContextFreeStructuresBudgetCertificate.controlled
    (c : IrreducibleContextFreeStructuresBudgetCertificate) : Prop :=
  0 < c.nonterminalWindow ∧
    c.irreducibilityWindow ≤
      c.nonterminalWindow + c.productionWindow + c.slack

def IrreducibleContextFreeStructuresBudgetCertificate.budgetControlled
    (c : IrreducibleContextFreeStructuresBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.nonterminalWindow + c.productionWindow +
      c.irreducibilityWindow + c.slack

def IrreducibleContextFreeStructuresBudgetCertificate.Ready
    (c : IrreducibleContextFreeStructuresBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def IrreducibleContextFreeStructuresBudgetCertificate.size
    (c : IrreducibleContextFreeStructuresBudgetCertificate) : ℕ :=
  c.nonterminalWindow + c.productionWindow + c.irreducibilityWindow + c.slack

theorem irreducibleContextFreeStructures_budgetCertificate_le_size
    (c : IrreducibleContextFreeStructuresBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleIrreducibleContextFreeStructuresBudgetCertificate :
    IrreducibleContextFreeStructuresBudgetCertificate :=
  { nonterminalWindow := 4
    productionWindow := 7
    irreducibilityWindow := 10
    certificateBudgetWindow := 22
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleIrreducibleContextFreeStructuresBudgetCertificate.Ready := by
  constructor
  · norm_num [IrreducibleContextFreeStructuresBudgetCertificate.controlled,
      sampleIrreducibleContextFreeStructuresBudgetCertificate]
  · norm_num [IrreducibleContextFreeStructuresBudgetCertificate.budgetControlled,
      sampleIrreducibleContextFreeStructuresBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleIrreducibleContextFreeStructuresBudgetCertificate.certificateBudgetWindow ≤
      sampleIrreducibleContextFreeStructuresBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleIrreducibleContextFreeStructuresBudgetCertificate.Ready := by
  constructor
  · norm_num [IrreducibleContextFreeStructuresBudgetCertificate.controlled,
      sampleIrreducibleContextFreeStructuresBudgetCertificate]
  · norm_num
      [IrreducibleContextFreeStructuresBudgetCertificate.budgetControlled,
        sampleIrreducibleContextFreeStructuresBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List IrreducibleContextFreeStructuresBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleIrreducibleContextFreeStructuresBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleIrreducibleContextFreeStructuresBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch7.IrreducibleContextFreeStructures
