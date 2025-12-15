/-
  AgentSpec Semantics

  This file contains the formal semantics for rule evaluation and enforcement,
  following Definition 3.2 (Rule Violation) and Definition 3.3 (AgentSpec Semantics).
-/

import AgentspecFormal.Basic
import AgentspecFormal.Events
import AgentspecFormal.Predicates
import AgentspecFormal.Enforcements
import AgentspecFormal.Rule

namespace AgentSpec

open Event

/-
from the interpreter.py:
```python
def enterCheckClause(self, ctx):
    for cond in ctx.predicate():
        self.check = self.check and self.eval_predicate(cond)
        if not self.check:
            break
```
all predicates must evaluate to true.
-/

structure EvalConfig where
  predicateTable : PredicateTable
  paramPredicateTable : ParamPredicateTable

def EvalConfig.default : EvalConfig :=
  { predicateTable := PredicateTable.empty
  , paramPredicateTable := fun _ => none }

structure CheckResult where
  passed : Bool
  evaluations : List (Pred × Bool)
  deriving Repr

def evalPredicate (cfg : EvalConfig) (ctx : PredicateContext) (p : Pred) : Bool :=
  p.eval cfg.predicateTable cfg.paramPredicateTable ctx

def evalChecks (cfg : EvalConfig) (ctx : PredicateContext) (checks : List Pred) : CheckResult :=
  let rec go (preds : List Pred) (acc : List (Pred × Bool)) : CheckResult :=
    match preds with
    | [] => { passed := true, evaluations := acc.reverse }
    | p :: ps =>
      let result := evalPredicate cfg ctx p
      if result then
        go ps ((p, true) :: acc)
      else
        { passed := false, evaluations := ((p, false) :: acc).reverse }
  go checks []

/-
from Definition 3.2 (AgentSpec Rule Violation):
"At any time step i, given user input u and the current trajectory τ_i,
a rule r is considered violated when:
1. The triggering event η_r occurs, AND
2. Every predicate p_r ∈ P_r evaluates to true"
-/

def isRuleTriggered (r : Rule) (eventCtx : EventContext) : Bool :=
  r.trigger.isTriggered eventCtx

def isRuleViolated (cfg : EvalConfig) (r : Rule) (eventCtx : EventContext)
    (predCtx : PredicateContext) : Bool :=
  isRuleTriggered r eventCtx && (evalChecks cfg predCtx r.checks).passed

structure RuleEvalResult where
  rule : Rule
  triggered : Bool
  violated : Bool
  checkResult : CheckResult
  deriving Repr

def evalRule (cfg : EvalConfig) (r : Rule) (eventCtx : EventContext)
    (predCtx : PredicateContext) : RuleEvalResult :=
  let triggered := isRuleTriggered r eventCtx
  let checkResult := if triggered then evalChecks cfg predCtx r.checks
                     else { passed := false, evaluations := [] }
  { rule := r
  , triggered := triggered
  , violated := triggered && checkResult.passed
  , checkResult := checkResult }

/-
From Definition 3.3 (AgentSpec Semantics):
"Given a user input u and the current trajectory τᵢ, each violated rule r
applies its enforcement functions eᵣ ∈ Eᵣ to update τᵢ, yielding a new
trajectory τ'ᵢ."
-/

structure EnforceRuleResult where
  rule : Rule
  enforced : Bool
  outcome : EnforcementOutcome
  deriving Repr

def enforceRule (r : Rule) (enfCtx : EnforcementContext) (env : EnforcementEnv)
    : EnforceRuleResult :=
  let outcome := applyEnforcements r.enforcements enfCtx env
  { rule := r
  , enforced := true
  , outcome := outcome }



structure ProgramEvalResult where
  ruleResults : List RuleEvalResult
  enforcement : Option EnforceRuleResult
  finalAction : Action
  deriving Repr

structure EvalContext where
  config : EvalConfig
  eventCtx : EventContext
  predCtx : PredicateContext
  enfCtx : EnforcementContext
  env : EnforcementEnv

/-
from controlled_agent_executor.py:
```python
def validate_and_enforce(self, action, state):
    for rule in self.rules:
        if rule.triggered(action.name, action.input):
            interpreter = RuleInterpreter(rule, state)
            result, action = interpreter.verify_and_enforce(action)
            if result == EnforceResult.CONTINUE:
                continue
            elif result in {SKIP, STOP}:
                return rule, action
            elif result == SELF_REFLECT:
                return self.validate_and_enforce(action, state)
    return None, action
```
-/
def evalProgram (program : Program) (ctx : EvalContext) : ProgramEvalResult :=
  let rec go (rules : List Rule) (results : List RuleEvalResult) (currentAction : Action)
      : ProgramEvalResult :=
    match rules with
    | [] =>
      { ruleResults := results.reverse
      , enforcement := none
      , finalAction := currentAction }
    | r :: rs =>
      let evalResult := evalRule ctx.config r ctx.eventCtx ctx.predCtx
      let results' := evalResult :: results
      if evalResult.violated then
        -- Apply enforcement
        let enfCtx' := { ctx.enfCtx with action := currentAction }
        let enfResult := enforceRule r enfCtx' ctx.env
        match enfResult.outcome.result with
        | EnforceResult.continue_ =>
          -- Continue to next rule with potentially modified action
          go rs results' enfResult.outcome.action
        | _ =>
          -- Stop evaluation, return result
          { ruleResults := results'.reverse
          , enforcement := some enfResult
          , finalAction := enfResult.outcome.action }
      else
        -- Rule not violated, continue to next rule
        go rs results' currentAction
  go program.rules [] ctx.enfCtx.action

/-
From Definition 3.3, enforcements transform trajectories:
- Stop: τ[:-1] → a_f sᵢ
- User Inspection: τᵢ (if permitted) or τᵢ → a_f sᵢ (if denied)
- Predefined Action: τᵢ → aₚ s'ᵢ
- LLM Self-Examination: τᵢ → a_c s'ᵢ
-/

def transformTrajectory (τ : Trajectory) (outcome : EnforcementOutcome)
    (newState : State) (obs : Observation) : Trajectory :=
  match outcome.result with
  -- action proceeds, add step to trajectory
  | EnforceResult.continue_ =>
    let step : Step := {
      fromState := τ.currentState
      action := outcome.action
      toState := newState
      observation := obs
    }
    τ.append step
  -- action skipped, no change to trajectory
  | EnforceResult.skip => τ
  -- execution stops, add finish step
  | EnforceResult.stop =>
    let step : Step := {
      fromState := τ.currentState
      action := Action.finish "Stopped by enforcement"
      toState := newState
      observation := obs
    }
    τ.append step
  -- self-reflection, trajectory continues with corrective action
  | EnforceResult.selfReflect =>
    let step : Step := {
      fromState := τ.currentState
      action := outcome.action
      toState := newState
      observation := obs
    }
    τ.append step

/-
from Definition 3.3:
"Given a function Eval(τᵢ, aᵢ), which evaluates the overall safety of the
trajectory and the current planned action according to the provided rules,
the goal of runtime enforcement is to guarantee that Eval(τᵢ, aᵢ) is safe
throughout the agent's operation."
-/

inductive SafetyResult
  | safe
  | unsafe_ (violatedRule : Rule) (reason : String)
  deriving Repr

/-- Evaluate safety of a trajectory and planned action -/
def evalSafety (cfg : EvalConfig) (program : Program) (τ : Trajectory)
    (plannedAction : Action) (userInput : UserInput) : SafetyResult :=
  let eventCtx : EventContext := {
    trajectory := τ
    previousState := if τ.steps.length > 0 then some (τ.slice 1).currentState else none
    currentAction := some plannedAction
    isFinishing := plannedAction.isFinish
  }
  let predCtx : PredicateContext := {
    userInput := userInput
    trajectory := τ
    action := some plannedAction
    toolInput := some plannedAction.input
  }
  let violatedRule := program.rules.find? fun r =>
    isRuleViolated cfg r eventCtx predCtx
  match violatedRule with
  | none => SafetyResult.safe
  | some r => SafetyResult.unsafe_ r s!"Rule {r.id} was violated"

end AgentSpec
