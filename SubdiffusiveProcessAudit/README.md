# Independent statement comparisons

Each comparison states a main theorem using only Mathlib definitions and the explicit mathematical vocabulary included in its challenge. Its solution imports the formalization and proves the same statement. The only intentionally unfinished proof is the final theorem in each `Challenge.lean`.

Comparison A checks the introduction Theorem A (`t.A`, `Paper.t_A_short`),
exposed as `SubdiffusiveProcess.process_convergence`. The precise scaling-limit
form (`t.scaling.limit`, `Paper.t_A`) is also exposed in MainTheorems as
`SubdiffusiveProcess.process_convergence_precise` and has a separate axiom report.

The comparator checks the statements and their definition dependencies, and allows only `propext`, `Classical.choice`, and `Quot.sound` in solutions. The challenge statements are checked separately against Mathlib.

Theorem C writes the induced anchored sample law as the defining pullback `Measure.comap Subtype.val M.P.toMeasure`. This is definitionally the underlying measure of the probability law used in the library theorem.
