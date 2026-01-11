# FreeCP - CP with context-free session types

Formalization of FreeCP, a version of CP with **context-free**
session types.

## Modules

* [Type](Type.agda): representation of recursive, polymorphic,
  context-free session types
* [Transitions](Transitions.agda): labelled transition system
  for context-free session types
* [Equivalence](Equivalence.agda): bisimulation and type
  equivalence
* [Process](Process.agda): intrinsically-typed representation
  of processes and typing rules
* [Congruence](Congruence.agda): pre-congruence relation and
  typing preservation for processes
* [Reduction](Reduction.agda): reduction relation and typing
  preservation for processes
* [DeadlockFreedom](DeadlockFreedom.agda): proof of deadlock freedom
* [Termination](Termination.agda): proof of strong termination
  and normalization function
