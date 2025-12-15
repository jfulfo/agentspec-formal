import AgentspecFormal.Basic
import AgentspecFormal.Events
import AgentspecFormal.Predicates
import AgentspecFormal.Enforcements
import AgentspecFormal.Rule
import AgentspecFormal.Semantics

namespace AgentSpec

/-
Predicate Independence
-/

/-- Predicate evaluation is independent of unused table entries.
    Two tables that agree on all entries produce the same evaluation. -/
theorem pred_eval_table_independent (p : Pred) (table₁ table₂ : PredicateTable)
    (paramTable₁ paramTable₂ : ParamPredicateTable) (ctx : PredicateContext)
    (h_table : ∀ name, table₁ name = table₂ name)
    (h_param : ∀ name, paramTable₁ name = paramTable₂ name) :
    p.eval table₁ paramTable₁ ctx = p.eval table₂ paramTable₂ ctx := by
  induction p with
  | true_ => rfl
  | false_ => rfl
  | not p ih => simp [Pred.eval, ih]
  | and p₁ p₂ ih₁ ih₂ => simp [Pred.eval, ih₁, ih₂]
  | or p₁ p₂ ih₁ ih₂ => simp [Pred.eval, ih₁, ih₂]
  | named id => simp [Pred.eval, h_table]
  | func name arg => simp only [Pred.eval, h_param]

theorem pred_double_negation (p : Pred) (table : PredicateTable)
    (paramTable : ParamPredicateTable) (ctx : PredicateContext) :
    (Pred.not (Pred.not p)).eval table paramTable ctx = p.eval table paramTable ctx := by
  simp [Pred.eval, Bool.not_not]

theorem pred_de_morgan_and (p₁ p₂ : Pred) (table : PredicateTable)
    (paramTable : ParamPredicateTable) (ctx : PredicateContext) :
    (Pred.not (Pred.and p₁ p₂)).eval table paramTable ctx =
    (Pred.or (Pred.not p₁) (Pred.not p₂)).eval table paramTable ctx := by
  simp [Pred.eval, Bool.not_and]

theorem pred_de_morgan_or (p₁ p₂ : Pred) (table : PredicateTable)
    (paramTable : ParamPredicateTable) (ctx : PredicateContext) :
    (Pred.not (Pred.or p₁ p₂)).eval table paramTable ctx =
    (Pred.and (Pred.not p₁) (Pred.not p₂)).eval table paramTable ctx := by
  simp [Pred.eval, Bool.not_or]

/- conjunction with false is always false (short-circuit property) -/
theorem pred_and_false_absorb (p : Pred) (table : PredicateTable)
    (paramTable : ParamPredicateTable) (ctx : PredicateContext) :
    (Pred.and Pred.false_ p).eval table paramTable ctx = false := by
  simp [Pred.eval]

/- disjunction with true is always true (short-circuit property) -/
theorem pred_or_true_absorb (p : Pred) (table : PredicateTable)
    (paramTable : ParamPredicateTable) (ctx : PredicateContext) :
    (Pred.or Pred.true_ p).eval table paramTable ctx = true := by
  simp [Pred.eval]

/- conjunction of a list is equivalent to checking all elements -/
theorem conj_eval_all (ps : List Pred) (table : PredicateTable)
    (paramTable : ParamPredicateTable) (ctx : PredicateContext) :
    (Pred.conj ps).eval table paramTable ctx = true ↔
    ∀ p ∈ ps, p.eval table paramTable ctx = true := by
  induction ps with
  | nil => simp [Pred.conj, Pred.eval]
  | cons p ps ih =>
    cases ps with
    | nil =>
      simp only [Pred.conj, List.mem_singleton]
      constructor
      · intro hp q hq; rw [hq]; exact hp
      · intro h; exact h p rfl
    | cons q qs =>
      unfold Pred.conj
      simp only [Pred.eval, Bool.and_eq_true, List.mem_cons]
      constructor
      · intro ⟨hp, hrest⟩ x hx
        cases hx with
        | inl heq => rw [heq]; exact hp
        | inr hmem => exact ih.mp hrest x (List.mem_cons.mpr hmem)
      · intro h
        constructor
        · exact h p (Or.inl rfl)
        · apply ih.mpr
          intro x hx
          exact h x (Or.inr (List.mem_cons.mp hx))

/-
Enforcement Soundness
-/

theorem enforcement_llm_depth_limit (ctx : EnforcementContext) (env : EnforcementEnv)
    (h : ctx.maxReflectionDepth ≤ ctx.reflectionDepth) :
    (Enforcement.llmSelfReflect.apply ctx env).result = EnforceResult.skip := by
  simp [Enforcement.apply, h]

theorem reflection_depth_bounds_iterations (ctx : EnforcementContext)
    (h : ctx.reflectionDepth < ctx.maxReflectionDepth) :
    (Enforcement.llmSelfReflect.apply ctx
      { userDecision := none, llmReflection := some ⟨Action.skip⟩ }).result
      = EnforceResult.selfReflect := by
  simp only [Enforcement.apply]
  have : ¬(ctx.maxReflectionDepth ≤ ctx.reflectionDepth) := Nat.not_le.mpr h
  simp [this]

theorem stop_always_terminates (ctx : EnforcementContext) (env : EnforcementEnv) :
    let outcome := Enforcement.stop.apply ctx env
    outcome.result = EnforceResult.stop ∧ outcome.action.isFinish = true := by
  simp [Enforcement.apply, Action.finish, Action.isFinish]

theorem user_rejection_prevents_action (ctx : EnforcementContext) :
    let env : EnforcementEnv := { userDecision := some UserDecision.reject, llmReflection := none }
    (Enforcement.userInspection.apply ctx env).result = EnforceResult.skip := by
  simp [Enforcement.apply]

theorem enforcement_seq_short_circuit (e : Enforcement) (es : List Enforcement)
    (ctx : EnforcementContext) (env : EnforcementEnv)
    (h : (e.apply ctx env).result ≠ EnforceResult.continue_) :
    applyEnforcements (e :: es) ctx env = e.apply ctx env := by
  simp [applyEnforcements]

theorem invoke_replaces_action (inv : ActionInvoke) (ctx : EnforcementContext)
    (env : EnforcementEnv) :
    ((Enforcement.invokeAction inv).apply ctx env |>.action.name) = inv.name := by
  simp [Enforcement.apply]

/-
Rule Properties
-/

open Event

theorem non_triggered_implies_not_violated (cfg : EvalConfig) (r : Rule)
    (eventCtx : EventContext) (predCtx : PredicateContext)
    (h : isRuleTriggered r eventCtx = false) :
    isRuleViolated cfg r eventCtx predCtx = false := by
  simp [isRuleViolated, h]

theorem empty_checks_violated_iff_triggered (cfg : EvalConfig) (r : Rule)
    (eventCtx : EventContext) (predCtx : PredicateContext)
    (h_empty : r.checks = []) :
    isRuleViolated cfg r eventCtx predCtx = isRuleTriggered r eventCtx := by
  simp [isRuleViolated, evalChecks, evalChecks.go, h_empty]

/- helper: evalChecks.go passed doesn't depend on accumulator -/
theorem evalChecks_go_passed_acc (cfg : EvalConfig) (ctx : PredicateContext)
    (checks : List Pred) (acc₁ acc₂ : List (Pred × Bool)) :
    (evalChecks.go cfg ctx checks acc₁).passed = (evalChecks.go cfg ctx checks acc₂).passed := by
  induction checks generalizing acc₁ acc₂ with
  | nil => rfl
  | cons p ps ih =>
    simp only [evalChecks.go]
    split
    · exact ih _ _
    · rfl

/- helper: evalChecks passes iff all predicates evaluate to true -/
theorem evalChecks_passed_iff (cfg : EvalConfig) (ctx : PredicateContext) (checks : List Pred) :
    (evalChecks cfg ctx checks).passed = true ↔
    ∀ p ∈ checks, evalPredicate cfg ctx p = true := by
  constructor
  · intro h p hp
    induction checks generalizing p with
    | nil => simp at hp
    | cons q qs ih =>
      simp only [evalChecks, evalChecks.go] at h
      split at h
      case isTrue hq =>
        cases hp with
        | head => exact hq
        | tail _ hmem =>
          unfold evalChecks at ih
          have hqs : (evalChecks.go cfg ctx qs [(q, true)]).passed = (evalChecks.go cfg ctx qs []).passed := by
            apply evalChecks_go_passed_acc
          rw [hqs] at h
          apply ih h
          exact hmem
      case isFalse => contradiction
  · intro h
    induction checks with
    | nil => simp [evalChecks, evalChecks.go]
    | cons q qs ih =>
      simp only [evalChecks, evalChecks.go]
      have hq := h q (List.Mem.head qs)
      simp only [hq, ↓reduceIte]
      have hrest := ih (fun p hp => h p (List.Mem.tail q hp))
      simp only [evalChecks] at hrest
      exact evalChecks_go_passed_acc cfg ctx qs [] _ ▸ hrest

/- rule violation is monotonic in checks: fewer checks means more violations -/
theorem fewer_checks_more_violations (cfg : EvalConfig) (r₁ r₂ : Rule)
    (eventCtx : EventContext) (predCtx : PredicateContext)
    (h_trigger : r₁.trigger = r₂.trigger)
    (h_subset : ∀ p, p ∈ r₁.checks → p ∈ r₂.checks)
    (h_violated : isRuleViolated cfg r₂ eventCtx predCtx = true) :
    isRuleViolated cfg r₁ eventCtx predCtx = true := by
  simp only [isRuleViolated, Bool.and_eq_true] at h_violated ⊢
  obtain ⟨h_trig, h_checks⟩ := h_violated
  constructor
  · simp only [isRuleTriggered, h_trigger]; exact h_trig
  · rw [evalChecks_passed_iff] at h_checks ⊢
    intro p hp
    exact h_checks p (h_subset p hp)

/- well-formed rule has non-empty enforcements -/
theorem well_formed_nonempty_enforcements (r : Rule) (h : r.isWellFormed = true) :
    r.enforcements ≠ [] := by
  simp [Rule.isWellFormed, Rule.hasEnforcements, Bool.not_eq_eq_eq_not,
    Bool.not_true, ne_eq] at h
  exact h

/-
Event Triggering Properties
-/

theorem state_change_needs_difference (ctx : EventContext)
    (h_some : ctx.previousState = some ctx.trajectory.currentState) :
    Event.isTriggered (Event.general GeneralEvent.stateChange) ctx = false := by
  simp [Event.isTriggered, h_some]

theorem domain_event_action_match (d : DomainEvent) (ctx : EventContext) (a : Action)
    (h_action : ctx.currentAction = some a) :
    Event.isTriggered (Event.domain d) ctx = (a.name == d.name) := by
  simp [Event.isTriggered, h_action]

theorem finish_event_on_finish_action (ctx : EventContext) (a : Action)
    (h_action : ctx.currentAction = some a)
    (h_finish : a.isFinish = true) :
    Event.isTriggered (Event.general GeneralEvent.agentFinish) ctx = true := by
  simp [Event.isTriggered, h_action, h_finish]

/-
Program Composition Properties
-/

def Program.compose (p₁ p₂ : Program) : Program :=
  { rules := p₁.rules ++ p₂.rules }

/- two programs have disjoint triggers if no rule in one triggers on the same
    event as any rule in the other -/
def Program.disjointTriggers (p₁ p₂ : Program) : Prop :=
  ∀ r₁ ∈ p₁.rules, ∀ r₂ ∈ p₂.rules, r₁.trigger ≠ r₂.trigger

/- two programs are independent if they have disjoint triggers and neither uses Event.any -/
def Program.independent (p₁ p₂ : Program) : Prop :=
  p₁.disjointTriggers p₂ ∧
  (∀ r ∈ p₁.rules, r.trigger ≠ Event.any) ∧
  (∀ r ∈ p₂.rules, r.trigger ≠ Event.any)


/- program composition preserves rule membership -/
theorem compose_rule_membership (p₁ p₂ : Program) (r : Rule) :
    r ∈ (p₁.compose p₂).rules ↔ r ∈ p₁.rules ∨ r ∈ p₂.rules := by
  simp [Program.compose]

/- adding rules can only introduce more violations (monotonicity) -/
theorem more_rules_more_violations (cfg : EvalConfig) (p : Program) (r : Rule)
    (τ : Trajectory) (action : Action) (userInput : UserInput) :
    evalSafety cfg p τ action userInput = SafetyResult.safe →
    evalSafety cfg (p.addRule r) τ action userInput = SafetyResult.safe →
    ¬isRuleViolated cfg r
      { trajectory := τ
        previousState := if τ.steps.length > 0 then some (τ.slice 1).currentState else none
        currentAction := some action
        isFinishing := action.isFinish }
      { userInput := userInput
        trajectory := τ
        action := some action
        toolInput := some action.input } := by
  intros _ h_safety_add
  simp only [evalSafety, Program.addRule] at h_safety_add
  split at h_safety_add
  case h_2 => contradiction
  case h_1 hfind =>
    rw [List.find?_eq_none] at hfind
    simp only [List.mem_append, List.mem_singleton] at hfind
    exact hfind r (Or.inr rfl)

/- if composition is safe, both components are safe -/
theorem safe_composition_implies_parts_safe (cfg : EvalConfig) (p₁ p₂ : Program)
    (τ : Trajectory) (action : Action) (userInput : UserInput)
    (h : evalSafety cfg (p₁.compose p₂) τ action userInput = SafetyResult.safe) :
    evalSafety cfg p₁ τ action userInput = SafetyResult.safe ∧
    evalSafety cfg p₂ τ action userInput = SafetyResult.safe := by
  simp only [evalSafety, Program.compose] at h ⊢
  split at h
  case h_2 => contradiction
  case h_1 hfind =>
    rw [List.find?_eq_none] at hfind
    simp only [List.mem_append] at hfind
    let pred := fun r => isRuleViolated cfg r
      { trajectory := τ
        previousState := if τ.steps.length > 0 then some (τ.slice 1).currentState else none
        currentAction := some action
        isFinishing := action.isFinish }
      { userInput := userInput
        trajectory := τ
        action := some action
        toolInput := some action.input }
    have hfind₁ : List.find? pred p₁.rules = none := by
      rw [List.find?_eq_none]
      intro r hr
      exact hfind r (Or.inl hr)
    have hfind₂ : List.find? pred p₂.rules = none := by
      rw [List.find?_eq_none]
      intro r hr
      exact hfind r (Or.inr hr)
    rw [hfind₁, hfind₂]
    simp

/- if both programs are safe and they are independent, their composition is safe -/
theorem independent_programs_safe_composition (cfg : EvalConfig) (p₁ p₂ : Program)
    (τ : Trajectory) (action : Action) (userInput : UserInput)
    (h_indep : p₁.independent p₂) -- why don't we need this !!
    (h_safe₁ : evalSafety cfg p₁ τ action userInput = SafetyResult.safe)
    (h_safe₂ : evalSafety cfg p₂ τ action userInput = SafetyResult.safe) :
    evalSafety cfg (p₁.compose p₂) τ action userInput = SafetyResult.safe := by
  simp only [evalSafety, Program.compose] at *
  split at h_safe₁
  case h_2 => contradiction
  case h_1 hfind₁ =>
    split at h_safe₂
    case h_2 => contradiction
    case h_1 hfind₂ =>
      have hfind₁' := List.find?_eq_none.mp hfind₁
      have hfind₂' := List.find?_eq_none.mp hfind₂
      let pred := fun r => isRuleViolated cfg r
        { trajectory := τ
          previousState := if τ.steps.length > 0 then some (τ.slice 1).currentState else none
          currentAction := some action
          isFinishing := action.isFinish }
        { userInput := userInput
          trajectory := τ
          action := some action
          toolInput := some action.input }
      have hcomb : List.find? pred (p₁.rules ++ p₂.rules) = none := by
        rw [List.find?_eq_none]
        intro r hr
        simp only [List.mem_append] at hr
        cases hr with
        | inl hr₁ => exact hfind₁' r hr₁
        | inr hr₂ => exact hfind₂' r hr₂
      rw [hcomb]

/- if a rule is not violated individually, adding it to a safe program keeps it safe -/
theorem add_non_violated_rule_safe (cfg : EvalConfig) (p : Program) (r : Rule)
    (τ : Trajectory) (action : Action) (userInput : UserInput)
    (h_safe : evalSafety cfg p τ action userInput = SafetyResult.safe)
    (h_not_violated : isRuleViolated cfg r
      { trajectory := τ
        previousState := if τ.steps.length > 0 then some (τ.slice 1).currentState else none
        currentAction := some action
        isFinishing := action.isFinish }
      { userInput := userInput
        trajectory := τ
        action := some action
        toolInput := some action.input } = false) :
    evalSafety cfg (p.addRule r) τ action userInput = SafetyResult.safe := by
  simp only [evalSafety, Program.addRule] at h_safe ⊢
  split at h_safe
  case h_2 => contradiction
  case h_1 hfind =>
    have hfind' := List.find?_eq_none.mp hfind
    let pred := fun r => isRuleViolated cfg r
      { trajectory := τ
        previousState := if τ.steps.length > 0 then some (τ.slice 1).currentState else none
        currentAction := some action
        isFinishing := action.isFinish }
      { userInput := userInput
        trajectory := τ
        action := some action
        toolInput := some action.input }
    have hres : List.find? pred (p.rules ++ [r]) = none := by
      rw [List.find?_eq_none]
      intro r' hr'
      simp only [List.mem_append, List.mem_singleton] at hr'
      cases hr' with
      | inl hr' => exact hfind' r' hr'
      | inr hr' => simp only [hr', Bool.not_eq_true]; exact h_not_violated
    rw [hres]

/- well-formedness is preserved under composition -/
theorem compose_preserves_well_formed (p₁ p₂ : Program)
    (h₁ : p₁.isWellFormed = true) (h₂ : p₂.isWellFormed = true) :
    (p₁.compose p₂).isWellFormed = true := by
  simp only [Program.isWellFormed, Program.compose, List.all_append,
    Bool.and_eq_true] at *
  exact ⟨h₁, h₂⟩

/-
Trajectory Transformation Properties
-/

theorem skip_preserves_length (τ : Trajectory) (newState : State) (obs : Observation) :
    let outcome : EnforcementOutcome := { result := EnforceResult.skip, action := Action.skip, feedback := none }
    (transformTrajectory τ outcome newState obs).steps.length = τ.steps.length := by
  simp [transformTrajectory]

theorem continue_increases_length (τ : Trajectory) (action : Action) (newState : State)
    (obs : Observation) :
    let outcome : EnforcementOutcome := { result := EnforceResult.continue_, action := action, feedback := none }
    (transformTrajectory τ outcome newState obs).steps.length = τ.steps.length + 1 := by
  simp [transformTrajectory, Trajectory.append]

theorem stop_increases_length (τ : Trajectory) (action : Action) (newState : State)
    (obs : Observation) :
    let outcome : EnforcementOutcome := { result := EnforceResult.stop, action := action, feedback := none }
    (transformTrajectory τ outcome newState obs).steps.length = τ.steps.length + 1 := by
  simp [transformTrajectory, Trajectory.append]

theorem append_updates_current (τ : Trajectory) (step : Step) :
    (τ.append step).currentState = step.toState := by
  simp [Trajectory.append, Trajectory.currentState]

theorem slice_zero_identity (τ : Trajectory) :
    τ.slice 0 = τ := by
  simp [Trajectory.slice]

theorem slice_compose (τ : Trajectory) (i j : Nat) (h : i + j ≤ τ.steps.length) :
    (τ.slice i).slice j = τ.slice (i + j) := by
  simp [Trajectory.slice, List.take_take]
  omega

/-
Safety Invariants
-/

theorem no_violations_safe (cfg : EvalConfig) (program : Program) (τ : Trajectory)
    (action : Action) (userInput : UserInput)
    (h : ∀ r ∈ program.rules, isRuleViolated cfg r
      { trajectory := τ
        previousState := if τ.steps.length > 0 then some (τ.slice 1).currentState else none
        currentAction := some action
        isFinishing := action.isFinish }
      { userInput := userInput
        trajectory := τ
        action := some action
        toolInput := some action.input } = false) :
    evalSafety cfg program τ action userInput = SafetyResult.safe := by
  unfold evalSafety
  have hfind : List.find? (fun r => isRuleViolated cfg r
      { trajectory := τ
        previousState := if τ.steps.length > 0 then some (τ.slice 1).currentState else none
        currentAction := some action
        isFinishing := action.isFinish }
      { userInput := userInput
        trajectory := τ
        action := some action
        toolInput := some action.input }) program.rules = none := by
    rw [List.find?_eq_none]
    intro r hr
    simp only [Bool.not_eq_true]
    exact h r hr
  simp only [hfind]

theorem unsafe_identifies_rule (cfg : EvalConfig) (program : Program) (τ : Trajectory)
    (action : Action) (userInput : UserInput) (r : Rule) (reason : String)
    (h : evalSafety cfg program τ action userInput = SafetyResult.unsafe_ r reason) :
    r ∈ program.rules ∧ isRuleViolated cfg r
      { trajectory := τ
        previousState := if τ.steps.length > 0 then some (τ.slice 1).currentState else none
        currentAction := some action
        isFinishing := action.isFinish }
      { userInput := userInput
        trajectory := τ
        action := some action
        toolInput := some action.input } = true := by
  simp only [evalSafety] at h
  split at h
  case h_1 => exact absurd h (by simp)
  case h_2 r' hfind =>
    have hpred := List.find?_some hfind
    have hmem := List.mem_of_find?_eq_some hfind
    cases h
    exact ⟨hmem, hpred⟩

theorem empty_program_safe (cfg : EvalConfig) (τ : Trajectory)
    (action : Action) (userInput : UserInput) :
    evalSafety cfg Program.empty τ action userInput = SafetyResult.safe := by
  simp [evalSafety, Program.empty]

/-
Rule Ordering Properties
-/

/- violation detection is independent of rule order
    (for determining IF a violation exists, not which rule is blamed) -/
theorem violation_order_independent (cfg : EvalConfig) (rules : List Rule)
    (eventCtx : EventContext) (predCtx : PredicateContext) :
    (∃ r ∈ rules, isRuleViolated cfg r eventCtx predCtx = true) ↔
    (∃ r ∈ rules.reverse, isRuleViolated cfg r eventCtx predCtx = true) := by
  constructor
  · intro ⟨r, hr, hv⟩
    exact ⟨r, List.mem_reverse.mpr hr, hv⟩
  · intro ⟨r, hr, hv⟩
    have : r ∈ rules := by simpa using List.mem_reverse.mp hr
    exact ⟨r, this, hv⟩

/-
Enforcement Coverage
-/

/- every enforcement produces one of the four possible results -/
theorem enforcement_result_exhaustive (e : Enforcement) (ctx : EnforcementContext)
    (env : EnforcementEnv) :
    let r := (e.apply ctx env).result
    r = EnforceResult.continue_ ∨ r = EnforceResult.skip ∨
    r = EnforceResult.stop ∨ r = EnforceResult.selfReflect := by
  cases e <;> simp [Enforcement.apply]
  -- userInspection
  · cases env.userDecision with
    | none => right; left; rfl
    | some d => cases d with
      | approve => left; rfl
      | reject => right; left; rfl
  -- llmSelfReflect
  · split
    · right; left; rfl
    · cases env.llmReflection with
      | none => right; left; rfl
      | some _ => right; right; right; rfl

/- non-continue results halt further rule processing -/
theorem non_continue_halts_processing (r : Rule) (rs : List Rule) (ctx : EvalContext)
    (h_violated : isRuleViolated ctx.config r ctx.eventCtx ctx.predCtx = true)
    (h_result : (applyEnforcements r.enforcements ctx.enfCtx ctx.env).result
      ≠ EnforceResult.continue_) :
    (evalProgram { rules := r :: rs } ctx).enforcement.isSome = true := by
  simp only [evalProgram]
  simp only [evalProgram.go]
  have h_eval_violated : (evalRule ctx.config r ctx.eventCtx ctx.predCtx).violated = true := by
    simp only [evalRule, isRuleViolated, Bool.and_eq_true] at h_violated ⊢
    obtain ⟨h_trig, h_checks⟩ := h_violated
    simp only [h_trig, ↓reduceIte]
    exact ⟨trivial, h_checks⟩
  simp only [h_eval_violated, ↓reduceIte]
  simp only [enforceRule]
  cases h_out : (applyEnforcements r.enforcements _ ctx.env).result with
  | continue_ => exact absurd h_out h_result
  | skip => rfl
  | stop => rfl
  | selfReflect => rfl

/-
termination Properties
-/

/- applyEnforcements terminates because it recurses over a finite list -/
theorem applyEnforcements_terminates (es : List Enforcement) (ctx : EnforcementContext)
    (env : EnforcementEnv) :
    ∃ outcome : EnforcementOutcome, applyEnforcements es ctx env = outcome := by
  exact ⟨applyEnforcements es ctx env, rfl⟩

/- therefore evalProgram always terminates -/
theorem evalProgram_terminates (program : Program) (ctx : EvalContext) :
    ∃ result : ProgramEvalResult, evalProgram program ctx = result := by
  exact ⟨evalProgram program ctx, rfl⟩

end AgentSpec
