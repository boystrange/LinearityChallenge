# FreeCP - CP with context-free session types

Formalization of FreeCP, a version of CP with **context-free**
session types.

* [type representation](freecp/Type.agda) (recursive, polymorphic,
  context-free session types)
* [labelled transition system for types](freecp/Transitions.agda)
* [type equivalence](freecp/Equivalence.agda)
* [process representation](freecp/Process.agda) (includes support
  for polymorphic recursion)
* [congruence preserves typing](freecp/Congruence.agda)
* [reduction preserves typing](freecp/Reduction.agda)
* [deadlock freedom](freecp/DeadlockFreedom.agda)
* [strong termination](freecp/Termination.agda)
