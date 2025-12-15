/-
  AgentSpec Formal Specification

  A Lean 4 formalization of the AgentSpec domain-specific language for
  runtime enforcement of LLM agent behavior.

  Based on the paper:
  "AgentSpec: Customizable Runtime Enforcement for Safe and Reliable LLM Agents"
  by Haoyu Wang, Christopher M. Poskitt, and Jun Sun (ICSE '26)
-/

import AgentspecFormal.Basic
import AgentspecFormal.Events
import AgentspecFormal.Predicates
import AgentspecFormal.Enforcements
import AgentspecFormal.Rule
import AgentspecFormal.Semantics
import AgentspecFormal.Properties
