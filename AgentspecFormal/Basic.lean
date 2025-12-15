/-
  This file provides the foundational types and definitions for the AgentSpec

  Based on the paper:
  "AgentSpec: Customizable Runtime Enforcement for Safe and Reliable LLM Agents"
  by Wang, Poskitt, and Sun (ICSE '26)
-/

import Mathlib.Data.List.Basic
import Mathlib.Logic.Basic

namespace AgentSpec

abbrev ident := String
abbrev UserInput := String

/- Observation received from the environment after executing an action -/
structure Observation where
  content : String
  deriving DecidableEq, Repr

/- An action that an agent can take -/
structure Action where
  name : ident
  input : String
  deriving DecidableEq, Repr

namespace Action

def finish (output : String) : Action :=
  { name := "finish", input := output }

def skip : Action :=
  { name := "skip", input := "" }

def isFinish (a : Action) : Bool :=
  a.name == "finish"

def isSkip (a : Action) : Bool :=
  a.name == "skip"

end Action

/- represents the internal state of an LLM agent -/
structure State where
  id : Nat
  content : String
  deriving DecidableEq, Repr

/- a transition from one state to another via an action -/
structure Step where
  fromState : State
  action : Action
  toState : State
  observation : Observation
  deriving Repr

/- a trajectory is a sequence of state transitions -/
structure Trajectory where
  initialState : State
  steps : List Step
  deriving Repr

namespace Trajectory

def currentState (τ : Trajectory) : State :=
  match τ.steps.getLast? with
  | some step => step.toState
  | none => τ.initialState

def currentAction? (τ : Trajectory) : Option Action :=
  τ.steps.getLast?.map (·.action)

def actions (τ : Trajectory) : List Action :=
  τ.steps.map (·.action)

def observations (τ : Trajectory) : List Observation :=
  τ.steps.map (·.observation)

def states (τ : Trajectory) : List State :=
  τ.initialState :: τ.steps.map (·.toState)

def length (τ : Trajectory) : Nat :=
  τ.steps.length

/- τ[:-i] excludes the last i state transitions -/
def slice (τ : Trajectory) (i : Nat) : Trajectory :=
  { τ with steps := τ.steps.take (τ.steps.length - i) }

def append (τ : Trajectory) (step : Step) : Trajectory :=
  { τ with steps := τ.steps ++ [step] }

def empty (s₀ : State) : Trajectory :=
  { initialState := s₀, steps := [] }

end Trajectory

/- list of (action, observation) pairs representing execution history -/
abbrev IntermediateSteps := List (Action × String)

def Trajectory.toIntermediateSteps (τ : Trajectory) : IntermediateSteps :=
  τ.steps.map fun step => (step.action, step.observation.content)

end AgentSpec
