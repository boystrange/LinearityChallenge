# README

This is a solution in Agda of the [linearity
challenge](https://concurrentbenchmark.github.io) for the finite fragment of
**πLIN**[^1]. In addition to the [safety property](Safety.lagda.md), the
solution also proves two [deadlock freedom results](DeadlockFreedom.lagda.md) as
well as the soundness of subsumption for the **logical subtyping** of session
types[^2].

[^1]: Luca Ciccone and Luca Padovani, [An Infinitary Proof Theory of Linear
    Logic Ensuring Fair Termination in the Linear
    π-Calculus](http://dx.doi.org/10.4230/LIPIcs.CONCUR.2022.36), Proceedings of
    the 33rd International Conference on Concurrency Theory (CONCUR’22), pages
    36:1-36:18, 2022.

[^2]: Ross Horne and Luca Padovani, [A Logical Account of Subtyping for Session
    Types](http://dx.doi.org/10.1016/j.jlamp.2024.100986), Journal of Logical
    and Algebraic Methods in Programming, 2024.
