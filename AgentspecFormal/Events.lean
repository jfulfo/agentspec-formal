/-
  AgentSpec Events

  Events are the triggering conditions that activate rules. They can be:
  - General lifecycle events (state_change, before_action, after_action, agent_finish)
  - Domain-specific events (tool invocations like PythonREPL, Transfer, etc.)
-/

import AgentspecFormal.Basic

namespace AgentSpec

/-
from paper section 3.2

"Triggers are based on events monitored by AgentSpec during agent execution.
The event system is designed to be highly generalizable, allowing dynamic and
context-aware applications of rules across diverse domains."

three types of triggering events:
1. state change event: detected when current state differs from previous state
2. action event: occurs during executing an action
3. agent finish event: when the action denotes end of the current task
-/

inductive GeneralEvent
  | stateChange
  | beforeAction
  | afterAction
  | agentFinish
  deriving DecidableEq, Repr

structure DomainEvent where
  name : ident
  deriving DecidableEq, Repr

inductive Event
  | general (e : GeneralEvent)
  | domain (e : DomainEvent)
  | any -- matches all events
  deriving DecidableEq, Repr

namespace Event

def matchesAction (e : Event) (actionName : ident) : Bool :=
  match e with
  | general GeneralEvent.beforeAction => true
  | general GeneralEvent.afterAction => true
  | domain d => d.name == actionName
  | any => true
  | _ => false

def isStateChange (e : Event) : Bool :=
  match e with
  | general GeneralEvent.stateChange => true
  | _ => false

def isFinish (e : Event) : Bool :=
  match e with
  | general GeneralEvent.agentFinish => true
  | _ => false

def fromIdent (s : String) : Event :=
  match s with
  | "state_change" => general GeneralEvent.stateChange
  | "before_action" => general GeneralEvent.beforeAction
  | "after_action" => general GeneralEvent.afterAction
  | "finish" => general GeneralEvent.agentFinish
  | "any" => any
  | name => domain { name := name }

/- runtime context for event evaluation -/
structure EventContext where
  trajectory : Trajectory
  previousState : Option State
  currentAction : Option Action
  isFinishing : Bool
  deriving Repr

def isTriggered (e : Event) (ctx : EventContext) : Bool :=
  match e with
  | general GeneralEvent.stateChange =>
    match ctx.previousState with
    | some prev => ctx.trajectory.currentState != prev
    | none => false
  | general GeneralEvent.beforeAction =>
    ctx.currentAction.isSome && !ctx.isFinishing
  | general GeneralEvent.afterAction =>
    -- After action is triggered when we have a completed action
    ctx.trajectory.steps.length > 0
  | general GeneralEvent.agentFinish =>
    ctx.isFinishing ||
    (ctx.currentAction.map Action.isFinish |>.getD false)
  | domain d =>
    match ctx.currentAction with
    | some action => action.name == d.name
    | none => false
  | any => true

end Event

end AgentSpec
