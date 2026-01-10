This repository is meant to contain Agda formalizations of various versions of the Linear Calculus of Continuations, a version of the linear π-calculus based on linear logic.

* [LCC](lcc)
* [LCC](rec) with infinite types and recursive processes
* [FreeCP](freecp) with context-free session types, recursive processes, polymorphic recursion
	* [type representation](freecp/Type.agda) with support for recursive and polymorphic types
	* [type labeled transition system](freecp/Transitions.agda)
	* [type equivalence](freecp/Equivalence.agda)
	* [process representation](freecp/Process.agda) with support for polymorphic recursion
    * [congruence preserves typing](freecp/Congruence.agda)
	* [reduction preserves typing](freecp/Reduction.agda)
	* [deadlock freedom](freecp/DeadlockFreedom.agda)
	* [strong termination](freecp/Termination.agda)
