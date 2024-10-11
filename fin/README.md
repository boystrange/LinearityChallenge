# Solution to the linearity challenge

By Luca Padovani and Claudia Raffaelli

This is a solution in Agda of the [linearity
challenge](https://concurrentbenchmark.github.io), which concerns the
formalization of a calculus of binary sessions, of its type system and of a
**safety result** for well-typed processes.

Below is a summary of the main features of this formalization:

* Processes are **intrinsically typed** so that only well-typed processes can be
  represented by the [`Process`](Process.lagda.md) data type. This choice
  slightly complicates the representation of processes, but has some notable
  advantages. First of all, there is no need to define processes and typing
  rules separately, as these are conflated within the same data type. Second,
  structural precongruence and reduction preserve typing *by definition*. In
  particular, there is no need to prove a subject reduction result for the
  calculus.
* Linearity is enforced by means of a [**context splitting**
  predicate](Context.lagda.md) making sure that every channel is used *exactly
  once*.
* Channels are (implicitly) represented by *de Bruijn indexes*. The
  representation is only implicit in the sense that every reference to a channel
  makes use of context splitting for singling out the type of the channel being
  used and the remaining context. In this way, there is no need to define a
  separate predicate for expressing the membership of a given type association
  to a given typing context as is the case in other Agda formalizations of
  session calculi and languages[^3][^4].

The calculus being formalized is called **πLIN**[^1] and differs from the
calculus described in the challenge[^5] for two main reasons:

* πLIN is based on **multiplicative additive linear logic (MALL)** in the sense
  that its [types](Type.lagda.md) are MALL propositions and its typing rules are
  MALL proof rules. This property of πLIN has a notable impact in the
  formalization. In particular, there is no need to name the two endpoints of a
  session differently (as is the case in the calculus in the challenge
  description[^5]) because the typing rules guarantee that no *thread* (i.e.
  sequential process) can ever own both endpoints at the same time.
* πLIN channels are **linear** in the (strong) sense of the linear π-calculus:
  every channel can (and must) be used **exactly once**. Structured
  communications are modeled by the explicit creation and exchange of
  **continuation channels**. It is a known fact that binary sessions can be
  encoded in the linear π-calculus[^6], hence this choice does not limit the
  expressiveness of πLIN insofar binary sessions are concerned. In fact, and
  somewhat surprisingly, working with encoded sessions helps taming the
  complexity of the formalization because there is no need to "update" the type
  of a channel after each use: when a channel is used it is **consumed** and
  therefore removed from the typing context. The type of the continuation
  channel, being fresh, is simply **added** at the beginning of the residual
  typing context, which is a straightforward operation if typing contexts are
  represented as lists.

In addition to the [safety property](Safety.lagda.md), the solution also proves
two [deadlock freedom results](DeadlockFreedom.lagda.md) as well as the
soundness of [subsumption](Subtyping.lagda.md) for the **logical subtyping** of
session types[^2].

[^1]: Luca Ciccone and Luca Padovani, [An Infinitary Proof Theory of Linear
    Logic Ensuring Fair Termination in the Linear
    π-Calculus](http://dx.doi.org/10.4230/LIPIcs.CONCUR.2022.36), CONCUR 2022,
    36:1-36:18, 2022.

[^2]: Ross Horne and Luca Padovani, [A Logical Account of Subtyping for Session
    Types](http://dx.doi.org/10.1016/j.jlamp.2024.100986), Journal of Logical
    and Algebraic Methods in Programming, 2024.

[^3]: Luca Ciccone and Luca Padovani, [A Dependently Typed Linear π-Calculus in
    Agda](http://dx.doi.org/10.1145/3414080.3414109), PPDP 2020, 8:1-8:14, 2020.

[^4]: Peter Thiemann: [Intrinsically-Typed Mechanized Semantics for Session
    Types](https://doi.org/10.1145/3354166.3354184). PPDP 2019: 19:1-19:15,
    2019.

[^5]: Marco Carbone, David Castro-Perez, Francisco Ferreira, Lorenzo Gheri,
    Frederik Krogsdal Jacobsen, Alberto Momigliano, Luca Padovani, Alceste
    Scalas, Dawit Tirore, Martin Vassor, Nobuko Yoshida and Daniel Zackon, [The
    Concurrent Calculi Formalisation
    Benchmark](http://dx.doi.org/10.1007/978-3-031-62697-5_9), COORDINATION
    2024, 149-158, 2024.

[^6]: Ornela Dardha, Elena Giachino, Davide Sangiorgi, [Session types
    revisited](https://doi.org/10.1016/j.ic.2017.06.002), Information and
    Computation, 256: 253-286, 2017.
