# Theorem B: quantitative homogenization

This pair checks Theorem B, label `t.B`, exposed as
`SubdiffusiveProcess.quantitative_homogenization` and proved from
`SubdiffusiveProcess.Paper.t_B`.

**What `Challenge.lean` states.** For `0 ≤ L ≤ M`, let `A_{L,M}(x) = ahom_L⁻¹ a_L(3ᴹx)` on the
unit cube. The error `D_{L,M}` between the solutions of `−∇·(A_{L,M}∇u) = f`, `u = h` on the
boundary, and of the Poisson problem `−Δu = f`, `u = h`, is measured in `L²` for the solution
and in `H⁻¹` for the gradient and the flux. The statement has two parts: an estimate
`D_{L,M} ≤ Z_{L,M} δ^ϑ (‖f‖_{L²} + ‖h‖_{H²})` uniform in the cutoff, with `Z_{L,M} ≥ 1` bounded
in `Lᵠ`, and, at a fixed cutoff, a rate `3^(−α_hom(M−L))` with an exponent `α_hom(d)` chosen before
the cutoff. It also asserts that both Dirichlet problems have unique weak solutions, and that
the random variables are measurable for the σ-algebra of the coefficient.

**How to read the encoding.**

- *Negative norms.* `H⁻¹` is the volume-normalized dual of `H¹₀`: the supremum is over test
  functions with compact support in the open cube and normalized gradient. The norm of a vector
  field is the sum over its components. On the unit cube normalization changes nothing.
- *The `H²` norm* of the boundary datum is the sum of the `L²` sizes of the function, its gradient
  and its Hessian. Any equivalent `H²` norm gives the same theorem with different constants.
- *The effective diffusivity* `ahom_m` is the infimum over cube scales `n` of the normalized
  trace of the expected coarse-grained matrix of `a_m` on the cube of side `3ⁿ`. The paper
  defines it as the limit as `n → ∞`; the two agree because the scalar sequence is
  nonincreasing, by subadditivity of the coarse-grained energy.
- *The coarse-grained matrix* is defined through the paper's variational quantity `J`, in the
  general form of the coarse-graining theory, which allows non-symmetric coefficients. For the
  symmetric scalar coefficients here, the skew part `κ` is zero and the matrix is determined by
  the energy `J(U, p, 0)` of the paper.
- *Constants.* In part 2 the constant `C(L,q,d,δ)` and the exponent do not depend on the model,
  only on the listed parameters.

`SolutionBasic.lean` repeats the vocabulary of the challenge on the proof side;
`SolutionBridge.lean` translates it into the library's vocabulary; `Solution.lean` applies the
library theorem. None of them adds a hypothesis. The permitted axioms are `propext`,
`Classical.choice` and `Quot.sound`.
