# FreeCP - CP with context-free session types

Formalization of FreeCP, a version of CP with **context-free**
session types.

## Modules

* [Type](freecp/Type.agda) representation of recursive, polymorphic,
  context-free session types
* [Transitions](freecp/Transitions.agda) labelled transition system
  for context-free session types
* [Equivalence](freecp/Equivalence.agda) bisimulation and type
  equivalence
* [Process](freecp/Process.agda) intrinsically-typed representation
  of processes and typing rules
* [Congruence](freecp/Congruence.agda) pre-congruence relation and
  typing preservation for processes
* [Reduction](freecp/Reduction.agda) reduction relation and typing
  preservation for processes
* [DeadlockFreedom](freecp/DeadlockFreedom.agda) proof of deadlock freedom
* [Termination](freecp/Termination.agda) proof of strong termination
  and normalization function
