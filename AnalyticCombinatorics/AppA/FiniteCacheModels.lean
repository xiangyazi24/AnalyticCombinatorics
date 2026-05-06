import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite cache models.

Cache states are represented by lists of keys.  The definitions keep hit,
miss, and capacity checks executable.
-/

namespace AnalyticCombinatorics.AppA.FiniteCacheModels

def cacheHit (key : ℕ) (cache : List ℕ) : Bool :=
  cache.any (fun x => x == key)

def cacheMiss (key : ℕ) (cache : List ℕ) : Bool :=
  !(cacheHit key cache)

def cacheLoad (cache : List ℕ) : ℕ :=
  cache.length

def withinCapacity (cache : List ℕ) (capacity : ℕ) : Prop :=
  cacheLoad cache ≤ capacity

theorem cacheLoad_cons (x : ℕ) (cache : List ℕ) :
    cacheLoad (x :: cache) = cacheLoad cache + 1 := by
  simp [cacheLoad]

theorem withinCapacity_mono {cache : List ℕ} {a b : ℕ}
    (h : withinCapacity cache a) (hab : a ≤ b) :
    withinCapacity cache b := by
  unfold withinCapacity at *
  omega

def sampleCache : List ℕ :=
  [3, 1, 4, 1]

example : cacheHit 4 sampleCache = true := by
  native_decide

example : cacheMiss 2 sampleCache = true := by
  native_decide

example : withinCapacity sampleCache 5 := by
  norm_num [withinCapacity, cacheLoad, sampleCache]

structure CacheWindow where
  capacity : ℕ
  load : ℕ
  hits : ℕ
  misses : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CacheWindow.capacityReady (w : CacheWindow) : Prop :=
  w.load ≤ w.capacity

def CacheWindow.accessControlled (w : CacheWindow) : Prop :=
  w.hits + w.misses ≤ w.load + w.slack

def CacheWindow.ready (w : CacheWindow) : Prop :=
  w.capacityReady ∧ w.accessControlled

def CacheWindow.certificate (w : CacheWindow) : ℕ :=
  w.capacity + w.load + w.hits + w.misses + w.slack

theorem misses_le_certificate (w : CacheWindow) :
    w.misses ≤ w.certificate := by
  unfold CacheWindow.certificate
  omega

def sampleCacheWindow : CacheWindow :=
  { capacity := 5, load := 4, hits := 2, misses := 1, slack := 0 }

example : sampleCacheWindow.ready := by
  norm_num [sampleCacheWindow, CacheWindow.ready, CacheWindow.capacityReady,
    CacheWindow.accessControlled]


structure FiniteCacheModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteCacheModelsBudgetCertificate.controlled
    (c : FiniteCacheModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteCacheModelsBudgetCertificate.budgetControlled
    (c : FiniteCacheModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteCacheModelsBudgetCertificate.Ready
    (c : FiniteCacheModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteCacheModelsBudgetCertificate.size
    (c : FiniteCacheModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteCacheModels_budgetCertificate_le_size
    (c : FiniteCacheModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteCacheModelsBudgetCertificate :
    FiniteCacheModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleFiniteCacheModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteCacheModelsBudgetCertificate.controlled,
      sampleFiniteCacheModelsBudgetCertificate]
  · norm_num [FiniteCacheModelsBudgetCertificate.budgetControlled,
      sampleFiniteCacheModelsBudgetCertificate]

example :
    sampleFiniteCacheModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteCacheModelsBudgetCertificate.size := by
  apply finiteCacheModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteCacheModelsBudgetCertificate.controlled,
      sampleFiniteCacheModelsBudgetCertificate]
  · norm_num [FiniteCacheModelsBudgetCertificate.budgetControlled,
      sampleFiniteCacheModelsBudgetCertificate]

/-- Finite executable readiness audit for finite-cache certificates. -/
def finiteCacheModelsBudgetCertificateListReady
    (data : List FiniteCacheModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteCacheModelsBudgetCertificateList_readyWindow :
    finiteCacheModelsBudgetCertificateListReady
      [sampleFiniteCacheModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold finiteCacheModelsBudgetCertificateListReady
    sampleFiniteCacheModelsBudgetCertificate
  native_decide

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleFiniteCacheModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteCacheModelsBudgetCertificate.controlled,
      sampleFiniteCacheModelsBudgetCertificate]
  · norm_num [FiniteCacheModelsBudgetCertificate.budgetControlled,
      sampleFiniteCacheModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteCacheModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteCacheModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List FiniteCacheModelsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteCacheModelsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleFiniteCacheModelsBudgetCertificate
  native_decide
end AnalyticCombinatorics.AppA.FiniteCacheModels
