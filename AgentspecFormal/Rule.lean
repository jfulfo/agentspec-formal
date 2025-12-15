import AgentspecFormal.Basic
import AgentspecFormal.Events
import AgentspecFormal.Predicates
import AgentspecFormal.Enforcements

namespace AgentSpec

/-
from the paper section 3.1
"Each rule consists of five parts:
  1. rule: keyword marking the beginning, followed by unique identifier
  2. trigger: specifying the event that activates the rule
  3. check: conditions that must be satisfied (conjunctions of predicates)
  4. enforce: actions taken when rule is triggered
  5. end: keyword marking conclusion"
from grammar:
```
⟨Rule⟩ ::= rule ⟨Id⟩
           trigger ⟨Event⟩
           check ⟨Pred⟩*
           enforce ⟨Enforce⟩+
           end
```
-/

/-
from Definition 3.1:
"An AgentSpec rule r ∈ R is represented as a three-tuple r = (ηᵣ, Pᵣ, Eᵣ).
- ηᵣ is the triggering event
- Pᵣ is a set of predicate functions
- Eᵣ is a sequence of enforcement functions"
-/
structure Rule where
  id : ident
  trigger : Event
  checks : List Pred
  enforcements : List Enforcement
  deriving Repr

namespace Rule

def mk' (id : ident) (trigger : Event) (checks : List Pred) (enforcements : List Enforcement) : Rule :=
  { id := id, trigger := trigger, checks := checks, enforcements := enforcements }

def predicate (r : Rule) : Pred :=
  Pred.conj r.checks

def hasChecks (r : Rule) : Bool :=
  !r.checks.isEmpty

def hasEnforcements (r : Rule) : Bool :=
  !r.enforcements.isEmpty

def isWellFormed (r : Rule) : Bool :=
  r.hasEnforcements

end Rule

/-
from the grammar:
```
⟨Program⟩ ::= ⟨Rule⟩+
```
-/
structure Program where
  rules : List Rule
  deriving Repr

namespace Program

def empty : Program := { rules := [] }

def addRule (p : Program) (r : Rule) : Program :=
  { rules := p.rules ++ [r] }

def getRule (p : Program) (id : ident) : Option Rule :=
  p.rules.find? (·.id == id)

def getRulesForEvent (p : Program) (e : Event) : List Rule :=
  p.rules.filter fun r =>
    r.trigger == e || r.trigger == Event.any ||
    match r.trigger, e with
    | Event.domain d1, Event.domain d2 => d1.name == d2.name
    | _, _ => false

def getRulesForAction (p : Program) (actionName : ident) : List Rule :=
  p.rules.filter fun r => r.trigger.matchesAction actionName

/- program is well-formed if all rules are well-formed -/
def isWellFormed (p : Program) : Bool :=
  p.rules.all Rule.isWellFormed

def ruleIds (p : Program) : List ident :=
  p.rules.map (·.id)

def hasUniqueIds (p : Program) : Bool :=
  let ids := p.ruleIds
  ids.length == ids.eraseDups.length

end Program

/-
runtime state for rule evaluation from state.py:
```python
class RuleState(BaseModel):
    toolkit: str = ""
    action: Optional[Action] = None
    agent: Optional[...] = None
    intermediate_steps: Any
    user_input: Optional[...] = None
    merits: List[str] = []
    critiques: List[str] = []
    reflection_depth: int = 0
```
-/
structure RuleState where
  toolkit : ident
  action : Option Action
  intermediateSteps : IntermediateSteps
  userInput : UserInput
  merits : List String -- passed checks
  critiques : List String -- failed checks
  reflectionDepth : Nat
  deriving Repr

namespace RuleState

def initial (userInput : UserInput) : RuleState :=
  { toolkit := ""
  , action := none
  , intermediateSteps := []
  , userInput := userInput
  , merits := []
  , critiques := []
  , reflectionDepth := 0 }

def addMerit (s : RuleState) (m : String) : RuleState :=
  { s with merits := s.merits ++ [m] }

def addCritique (s : RuleState) (c : String) : RuleState :=
  { s with critiques := s.critiques ++ [c] }

def incrementReflection (s : RuleState) : RuleState :=
  { s with reflectionDepth := s.reflectionDepth + 1 }

def toPredicateContext (s : RuleState) (trajectory : Trajectory) : PredicateContext :=
  { userInput := s.userInput,
    trajectory := trajectory,
    action := s.action,
    toolInput := s.action.map (·.input) }

def toEnforcementContext (s : RuleState) (trajectory : Trajectory) (action : Action) : EnforcementContext :=
  { trajectory := trajectory,
    action := action,
    userInput := s.userInput,
    reflectionDepth := s.reflectionDepth }

end RuleState

end AgentSpec
