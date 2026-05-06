import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite grammar models.

The record stores terminal, nonterminal, and production budgets for
finite grammar schemas.
-/

namespace AnalyticCombinatorics.AppA.FiniteGrammarModels

structure GrammarData where
  terminals : ℕ
  nonterminals : ℕ
  productions : ℕ
deriving DecidableEq, Repr

def grammarAlphabetNonempty (d : GrammarData) : Prop :=
  0 < d.terminals + d.nonterminals

def productionsControlled (d : GrammarData) : Prop :=
  d.productions ≤ d.terminals + d.nonterminals

def grammarReady (d : GrammarData) : Prop :=
  grammarAlphabetNonempty d ∧ productionsControlled d

def grammarBudget (d : GrammarData) : ℕ :=
  d.terminals + d.nonterminals + d.productions

theorem grammarReady.alphabet {d : GrammarData} (h : grammarReady d) :
    grammarAlphabetNonempty d ∧ productionsControlled d ∧ d.productions ≤ grammarBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold grammarBudget
  omega

theorem terminals_le_grammarBudget (d : GrammarData) :
    d.terminals ≤ grammarBudget d := by
  unfold grammarBudget
  omega

def sampleGrammarData : GrammarData :=
  { terminals := 4, nonterminals := 5, productions := 7 }

example : grammarReady sampleGrammarData := by
  norm_num [grammarReady, grammarAlphabetNonempty]
  norm_num [productionsControlled, sampleGrammarData]

example : grammarBudget sampleGrammarData = 16 := by
  native_decide

structure GrammarWindow where
  terminals : ℕ
  nonterminals : ℕ
  productions : ℕ
  derivationBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def GrammarWindow.productionsControlled (w : GrammarWindow) : Prop :=
  w.productions ≤ w.terminals + w.nonterminals + w.slack

def GrammarWindow.derivationControlled (w : GrammarWindow) : Prop :=
  w.derivationBudget ≤ w.terminals + w.nonterminals + w.productions + w.slack

def grammarWindowReady (w : GrammarWindow) : Prop :=
  0 < w.terminals + w.nonterminals ∧
    w.productionsControlled ∧
    w.derivationControlled

def GrammarWindow.certificate (w : GrammarWindow) : ℕ :=
  w.terminals + w.nonterminals + w.productions + w.slack

theorem grammar_derivationBudget_le_certificate {w : GrammarWindow}
    (h : grammarWindowReady w) :
    w.derivationBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hderivation⟩
  exact hderivation

def sampleGrammarWindow : GrammarWindow :=
  { terminals := 4, nonterminals := 5, productions := 7, derivationBudget := 15, slack := 0 }

example : grammarWindowReady sampleGrammarWindow := by
  norm_num [grammarWindowReady, GrammarWindow.productionsControlled,
    GrammarWindow.derivationControlled, sampleGrammarWindow]

example : sampleGrammarWindow.certificate = 16 := by
  native_decide


structure FiniteGrammarModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteGrammarModelsBudgetCertificate.controlled
    (c : FiniteGrammarModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteGrammarModelsBudgetCertificate.budgetControlled
    (c : FiniteGrammarModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteGrammarModelsBudgetCertificate.Ready
    (c : FiniteGrammarModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteGrammarModelsBudgetCertificate.size
    (c : FiniteGrammarModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteGrammarModels_budgetCertificate_le_size
    (c : FiniteGrammarModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteGrammarModelsBudgetCertificate :
    FiniteGrammarModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteGrammarModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteGrammarModelsBudgetCertificate.controlled,
      sampleFiniteGrammarModelsBudgetCertificate]
  · norm_num [FiniteGrammarModelsBudgetCertificate.budgetControlled,
      sampleFiniteGrammarModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteGrammarModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteGrammarModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteGrammarModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteGrammarModelsBudgetCertificate.controlled,
      sampleFiniteGrammarModelsBudgetCertificate]
  · norm_num [FiniteGrammarModelsBudgetCertificate.budgetControlled,
      sampleFiniteGrammarModelsBudgetCertificate]

example :
    sampleFiniteGrammarModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteGrammarModelsBudgetCertificate.size := by
  apply finiteGrammarModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteGrammarModelsBudgetCertificate.controlled,
      sampleFiniteGrammarModelsBudgetCertificate]
  · norm_num [FiniteGrammarModelsBudgetCertificate.budgetControlled,
      sampleFiniteGrammarModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List FiniteGrammarModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteGrammarModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteGrammarModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteGrammarModels
