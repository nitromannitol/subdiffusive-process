# Process convergence comparator

This pair checks introductory Theorem A, labelled `t.A` in the paper and exposed
as `SubdiffusiveProcess.process_convergence`, from `Paper.t_A_short`.
The precise scaling-limit theorem, labelled `t.scaling.limit`, is exposed
separately as `SubdiffusiveProcess.process_convergence_precise`.

The Challenge retains the weak-resolvent and finite-dimensional attachments of
the analytic path laws. It states annealed convergence, reversible singular
limiting measures and transition laws, exit bounds for every side length in
`(0,1]`, and the infinite extended-real limsup for every exponent above the
subdiffusive threshold.

`Challenge.lean` imports only Mathlib and contains one intentional principal
`sorry`. `SolutionBasic.lean` supplies exactly the same isolated vocabulary.
`Solution.lean` converts that vocabulary and applies the public short theorem
without adding a hypothesis or dropping a conclusion. The permitted axioms
are `propext`, `Classical.choice` and `Quot.sound`.

Final standalone compilation and comparator verification against the selected
v4.35 release remain pending. Verification of a staging copy is separate from
that release gate.
