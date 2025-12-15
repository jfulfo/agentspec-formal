
import AgentspecFormal.Basic
import AgentspecFormal.Events

namespace AgentSpec

/-
  predicates are the conditions that are checked when a rule is triggered.
-/

/-
from Definition 3.1 (AgentSpec Rule):
"The second component, Pᵣ, is a set of predicate functions."

each predicate pᵣ ∈ Pᵣ evaluates to a Boolean value:
  pᵣ(u, τᵢ) ∈ B

the inputs to predicate functions depend on the type of trigger event:
- for state change: requires only current state sᵢ
- for action event: requires both current state sᵢ and action aᵢ
-/

structure PredicateContext where
  userInput : UserInput
  trajectory : Trajectory
  action : Option Action
  /- tool input for action-based predicates -/
  toolInput : Option String
  deriving Repr

/- abstract predicate function type -/
def PredicateFn := PredicateContext → Bool

/-- Domain-specific predicate identifier -/
structure PredicateId where
  name : ident
  deriving DecidableEq, Repr, Inhabited

/-
predicate: TRUE | FALSE | NOT predicate | PREDICATE | predicate_func
predicate_func: IDENTIFIER LPAREN number RPAREN
-/
inductive Pred
  | true_
  | false_
  | not (p : Pred)
  | and (p₁ p₂ : Pred)
  | or (p₁ p₂ : Pred)
  | named (id : PredicateId)
  | func (name : ident) (arg : Int)
  deriving DecidableEq, Repr

namespace Pred

def conj (ps : List Pred) : Pred :=
  match ps with
  | [] => true_
  | [p] => p
  | p :: ps => and p (conj ps)

def disj (ps : List Pred) : Pred :=
  match ps with
  | [] => false_
  | [p] => p
  | p :: ps => or p (disj ps)

end Pred

/-
a predicate table maps predicate identifiers to their implementations.
in the actual implementation, these are python functions, but here we abstract
them as functions from PredicateContext to Bool.
-/
def PredicateTable := ident → Option PredicateFn

def PredicateTable.empty : PredicateTable := fun _ => none

def PredicateTable.insert (table : PredicateTable) (name : ident) (fn : PredicateFn) : PredicateTable :=
  fun n => if n == name then some fn else table n

def ParamPredicateTable := ident → Option (Int → PredicateFn)

/-
from the interpreter.py:
```python
def eval_predicate(self, ctx) -> bool:
    if ctx.TRUE():
        return True
    elif ctx.FALSE():
        return False
    elif ctx.NOT():
        return not self.eval_predicate(ctx.predicate())
    elif ctx.PREDICATE():
        func = predicate_table[predicate_str]
        return func(user_input, tool_input, intermediate_steps)
```
-/
def Pred.eval (table : PredicateTable) (paramTable : ParamPredicateTable) (ctx : PredicateContext) : Pred → Bool
  | true_ => true
  | false_ => false
  | not p => !(eval table paramTable ctx p)
  | and p₁ p₂ => eval table paramTable ctx p₁ && eval table paramTable ctx p₂
  | or p₁ p₂ => eval table paramTable ctx p₁ || eval table paramTable ctx p₂
  | named id =>
    match table id.name with
    | some fn => fn ctx
    | none => false  -- unknown predicate evaluates to false
  | func name arg =>
    match paramTable name with
    | some fn => fn arg ctx
    | none => false


-- some example predicates from the paper's implementation.
def alwaysTrue : PredicateFn := fun _ => true

def alwaysFalse : PredicateFn := fun _ => false

def containsString (s : String) : PredicateFn := fun ctx =>
  match ctx.toolInput with
  | some input => input.contains s
  | none => false

end AgentSpec
