import AgentspecFormal.Basic
import AgentspecFormal.Events
import AgentspecFormal.Predicates

namespace AgentSpec

/-
  from the paper section 3.2:
  "Enforcements are the interventions taken by AgentSpec when a rule is
  triggered and the conditions are satisfied."
-/

/-
from enforcement.py:
```python
class EnforceResult(Enum):
    CONTINUE = 0   # Allow action to proceed
    SKIP = 1       # Skip the action
    STOP = 2       # Stop execution entirely
    SELF_REFLECT = 3  # Ask LLM to reconsider
```
-/
inductive EnforceResult
  | continue_
  | skip
  | stop
  | selfReflect
  deriving DecidableEq, Repr

/-
```
ENFORCEMENT: 'user_inspection' | 'llm_self_reflect' | 'stop' | 'none' | 'skip'
enforcement: ENFORCEMENT | actionInvoke | config
```
-/
structure KVPair where
  key : String
  value : String
  deriving DecidableEq, Repr

instance : ToString KVPair where
  toString := fun kv => kv.key ++ " " ++ kv.value

structure ActionInvoke where
  name : ident
  args : List KVPair
  deriving DecidableEq, Repr

structure Config where
  dslNamespace : List ident
  name : ident
  value : Int
  deriving DecidableEq, Repr

/- enforcement syntax

from the paper section 3.2:
- user_inspection: prompts user to inspect and confirm
- llm_self_examine: activates LLM-based self-examination
- invoke_action: executes a specific action with parameters
- stop: terminates the agent
- none: no enforcement (allow action to proceed)
- skip: skip the current action
-/
inductive Enforcement
  | no
  | skip
  | stop
  | userInspection
  | llmSelfReflect
  | invokeAction (action : ActionInvoke)
  | config (cfg : Config)
  deriving DecidableEq, Repr

namespace Enforcement

def fromString (s : String) : Enforcement :=
  match s with
  | "none" => no
  | "skip" => skip
  | "stop" => stop
  | "user_inspection" => userInspection
  | "llm_self_reflect" => llmSelfReflect
  | _ => no

end Enforcement

/-
from definition 3.3:
an enforcement eᵣ ∈ Eᵣ transforms the current trajectory τᵢ as follows:
1. stop: trajectory is terminated
2. user inspection: agent pauses for user approval
3. predefined Action: given action aₚ is executed
4. llm self-examination: corrective response is generated
-/
structure EnforcementOutcome where
  result : EnforceResult
  action : Action
  feedback : Option String
  deriving Repr

structure EnforcementContext where
  trajectory : Trajectory
  action : Action
  userInput : UserInput
  reflectionDepth : Nat
  maxReflectionDepth : Nat := 3
  deriving Repr

/-
for formal reasoning, we model enforcement application as a pure function
that transforms the context. side effects (user input, LLM calls) are
modeled abstractly.
-/

inductive UserDecision
  | approve
  | reject
  deriving DecidableEq, Repr

structure LLMReflection where
  correctiveAction : Action
  deriving Repr

structure EnforcementEnv where
  userDecision : Option UserDecision
  llmReflection : Option LLMReflection
  deriving Repr

/-
from the paper definition 3.3 and controlled_agent_executor.py:
-/
def Enforcement.apply (e : Enforcement) (ctx : EnforcementContext) (env : EnforcementEnv) : EnforcementOutcome :=
  match e with
  | no =>
    { result := EnforceResult.continue_, action := ctx.action, feedback := none }
  | skip =>
    { result := EnforceResult.skip,
      action := Action.skip,
      feedback := some "Action skipped by rule" }
  | stop =>
    { result := EnforceResult.stop,
      action := Action.finish "Execution stopped by rule",
      feedback := some "Execution stopped by enforcement rule" }
  | userInspection =>
    match env.userDecision with
    | some UserDecision.approve =>
      { result := EnforceResult.continue_,
        action := ctx.action,
        feedback := some "User approved action" }
    | some UserDecision.reject =>
      { result := EnforceResult.skip,
        action := Action.skip,
        feedback := some "User rejected action" }
    | none =>
      -- if no user decision provided, default to blocking
      { result := EnforceResult.skip,
        action := Action.skip,
        feedback := some "Awaiting user inspection" }
  | llmSelfReflect =>
    if ctx.reflectionDepth >= ctx.maxReflectionDepth then
      { result := EnforceResult.skip,
        action := Action.skip,
        feedback := some "Max reflection depth exceeded" }
    else
      match env.llmReflection with
      | some reflection =>
        { result := EnforceResult.selfReflect,
          action := reflection.correctiveAction,
          feedback := some "LLM generated corrective action" }
      | none =>
        { result := EnforceResult.skip,
          action := Action.skip,
          feedback := some "No LLM reflection available" }
  | invokeAction invocation =>
    let newAction := { name := invocation.name, input := toString invocation.args : Action }
    { result := EnforceResult.continue_,
      action := newAction,
      feedback := some "Replaced with predefined action" }
  | config _ =>
    { result := EnforceResult.continue_,
      action := ctx.action,
      feedback := some "Configuration applied" }

/- apply a sequence of enforcements, stopping at the first non-continue result -/
def applyEnforcements (enforcements : List Enforcement) (ctx : EnforcementContext) (env : EnforcementEnv)
    : EnforcementOutcome :=
  match enforcements with
  | [] => { result := EnforceResult.continue_, action := ctx.action, feedback := none }
  | e :: es =>
    let outcome := e.apply ctx env
    match outcome.result with
    | EnforceResult.continue_ =>
      let newCtx := { ctx with action := outcome.action }
      applyEnforcements es newCtx env
    | _ => outcome

end AgentSpec
