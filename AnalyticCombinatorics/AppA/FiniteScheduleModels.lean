import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite schedule models.

Schedules are represented by task durations.  The file records finite load,
deadline, and slack calculations.
-/

namespace AnalyticCombinatorics.AppA.FiniteScheduleModels

def scheduleLoad (tasks : List ℕ) : ℕ :=
  tasks.sum

def taskCount (tasks : List ℕ) : ℕ :=
  tasks.length

def meetsDeadline (tasks : List ℕ) (deadline : ℕ) : Prop :=
  scheduleLoad tasks ≤ deadline

def deadlineSlack (tasks : List ℕ) (deadline : ℕ) : ℕ :=
  deadline - scheduleLoad tasks

theorem scheduleLoad_cons (x : ℕ) (tasks : List ℕ) :
    scheduleLoad (x :: tasks) = x + scheduleLoad tasks := by
  simp [scheduleLoad]

theorem taskCount_cons (x : ℕ) (tasks : List ℕ) :
    taskCount (x :: tasks) = taskCount tasks + 1 := by
  simp [taskCount]

theorem deadlineSlack_add {tasks : List ℕ} {deadline : ℕ}
    (h : meetsDeadline tasks deadline) :
    deadlineSlack tasks deadline + scheduleLoad tasks = deadline := by
  unfold deadlineSlack meetsDeadline at *
  omega

def sampleSchedule : List ℕ :=
  [3, 1, 4, 2]

example : scheduleLoad sampleSchedule = 10 := by
  native_decide

example : taskCount sampleSchedule = 4 := by
  native_decide

example : meetsDeadline sampleSchedule 12 := by
  norm_num [meetsDeadline, scheduleLoad, sampleSchedule]

structure ScheduleWindow where
  tasks : ℕ
  load : ℕ
  deadline : ℕ
  criticalTasks : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ScheduleWindow.deadlineReady (w : ScheduleWindow) : Prop :=
  w.load ≤ w.deadline + w.slack

def ScheduleWindow.criticalControlled (w : ScheduleWindow) : Prop :=
  w.criticalTasks ≤ w.tasks

def ScheduleWindow.ready (w : ScheduleWindow) : Prop :=
  w.deadlineReady ∧ w.criticalControlled

def ScheduleWindow.certificate (w : ScheduleWindow) : ℕ :=
  w.tasks + w.load + w.deadline + w.criticalTasks + w.slack

theorem tasks_le_certificate (w : ScheduleWindow) :
    w.tasks ≤ w.certificate := by
  unfold ScheduleWindow.certificate
  omega

def sampleScheduleWindow : ScheduleWindow :=
  { tasks := 4, load := 10, deadline := 12, criticalTasks := 2, slack := 0 }

example : sampleScheduleWindow.ready := by
  norm_num [sampleScheduleWindow, ScheduleWindow.ready,
    ScheduleWindow.deadlineReady, ScheduleWindow.criticalControlled]


structure FiniteScheduleModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteScheduleModelsBudgetCertificate.controlled
    (c : FiniteScheduleModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteScheduleModelsBudgetCertificate.budgetControlled
    (c : FiniteScheduleModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteScheduleModelsBudgetCertificate.Ready
    (c : FiniteScheduleModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteScheduleModelsBudgetCertificate.size
    (c : FiniteScheduleModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteScheduleModels_budgetCertificate_le_size
    (c : FiniteScheduleModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteScheduleModelsBudgetCertificate :
    FiniteScheduleModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleFiniteScheduleModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteScheduleModelsBudgetCertificate.controlled,
      sampleFiniteScheduleModelsBudgetCertificate]
  · norm_num [FiniteScheduleModelsBudgetCertificate.budgetControlled,
      sampleFiniteScheduleModelsBudgetCertificate]

example :
    sampleFiniteScheduleModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteScheduleModelsBudgetCertificate.size := by
  apply finiteScheduleModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteScheduleModelsBudgetCertificate.controlled,
      sampleFiniteScheduleModelsBudgetCertificate]
  · norm_num [FiniteScheduleModelsBudgetCertificate.budgetControlled,
      sampleFiniteScheduleModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleFiniteScheduleModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteScheduleModelsBudgetCertificate.controlled,
      sampleFiniteScheduleModelsBudgetCertificate]
  · norm_num [FiniteScheduleModelsBudgetCertificate.budgetControlled,
      sampleFiniteScheduleModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteScheduleModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteScheduleModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List FiniteScheduleModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteScheduleModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteScheduleModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteScheduleModels
