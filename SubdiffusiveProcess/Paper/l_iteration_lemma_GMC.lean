import SubdiffusiveProcess.Paper.lane4_deterministic_iteration_input

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Paper

/-- Lemma `l.iteration.lemma.GMC` (deterministic iteration lemma): the complete proposition
`lane4_deterministic_iteration_input d` (all clauses: the slope bound and the excess decay with the
bounded-error parameter; the constant `C(d)` precedes `h`, `θ`, the scales, the domains and the data),
discharged by the frozen deterministic iteration lemma of the GMC library. -/
theorem l_iteration_lemma_GMC (d : ℕ) : Paper.lane4_deterministic_iteration_input d :=
  SubdiffusiveProcess.Frozen.Section6.iteration_lemma d

end Paper
