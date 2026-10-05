# Independent statement comparisons

The three main theorems of the paper (A, B and C) are each restated here using nothing but
Mathlib and the mathematical vocabulary that the restatement itself defines. Each
restatement is then proved from the library, and
[leanprover/comparator](https://github.com/leanprover/comparator) checks that the statement
proved from the library is the restated one. A reader who wants to know what a main theorem
says therefore needs only the corresponding `Challenge.lean`, not the library.

## How a pair is built and checked

Each subdirectory is one comparator pair:

| File | Role |
| --- | --- |
| `Challenge.lean` | The statement. It imports Mathlib only, defines every notion that the statement uses, and has exactly one `sorry`, the proof of the final theorem. **This is the file to read.** |
| `Solution.lean` | The proof. It states the same theorem and proves it from the library. |
| `SolutionBasic.lean` | The vocabulary of the challenge, compiled on the proof side, so that the solution can state the same theorem. |
| `SolutionBridge.lean` | Present for B and C. It translates between the challenge's vocabulary and the library's. |
| `comparator.json` | The comparator configuration: the challenge and solution modules, the theorem name, and the permitted axioms. |

`SolutionBasic.lean` and `SolutionBridge.lean` are proof infrastructure. They add no
hypothesis to the statement: the comparator compares the theorem in the challenge with the
theorem in the solution, together with the definitions that the statement depends on.
`comparator.json` permits exactly `propext`, `Classical.choice` and `Quot.sound`, and the
comparator replays the solution with independent implementations of the Lean kernel.
The key `enable_nanoda` is set, so the pinned-tool route also replays with NanoDa; the route
using the tools bundled with the toolchain always checks with Lean, NanoDa and con-ron. See the
[README](../README.md#running-the-comparators) for how to run them.

## The pairs

| Pair | Paper statement | Library declaration |
| --- | --- | --- |
| [`ProcessConvergence`](ProcessConvergence/) | Theorem A, label `t.A` | `SubdiffusiveProcess.process_convergence` |
| [`QuantitativeHomogenization`](QuantitativeHomogenization/) | Theorem B, label `t.B` | `SubdiffusiveProcess.quantitative_homogenization` |
| [`AnomalousHolderRegularity`](AnomalousHolderRegularity/) | Theorem C, label `t.C` | `SubdiffusiveProcess.anomalous_holder_regularity` |

The precise form of Theorem A (`t.scaling.limit`, `SubdiffusiveProcess.process_convergence_precise`)
has no separate pair; it has its own axiom report, which the build checks.

## Conventions shared by the challenges

- Every theorem is stated for an arbitrary model: independent layers of locally `C¹ˑ¹`
  potentials with the exact triadic scaling, and the paper's assumptions (g1)–(g4), in
  dimension at least two. The challenges define this model themselves. As in the library,
  models are supplied, not constructed; see the README.
- Cubes and balls use the sup norm, quadratic energies the Euclidean norm.
- Real-valued definitions are total, so analytic statements carry the positivity,
  finiteness and integrability hypotheses that they need.
- Where Mathlib has no canonical structure (for example a σ-algebra on spaces of continuous
  functions), the challenge takes the structure as an instance argument. The Borel structure
  of a topological space is unique, so this is not a loss of generality.
