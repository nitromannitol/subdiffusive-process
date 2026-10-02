import SubdiffusiveProcess.Assumptions.AnchoredPartialSum

/-!
# Anchored local `C¹ˑ¹` convergence
-/

open Filter Homogenization Topology

/-- Values and stored derivatives of the finite anchored sums converge
uniformly on compact sets, while their derivatives are Cauchy in every compact
Lipschitz seminorm. -/

structure SubdiffusiveProcess.Frozen.Assumptions.IsAnchoredC11Limit {d : ℕ}
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) : Prop where
  value_tendsto : ∀ K : Set (Vec d), IsCompact K →
    TendstoUniformlyOn
      (fun L x ↦ SubdiffusiveProcess.Frozen.Assumptions.anchoredPartialSum omega L x)
      g atTop K
  deriv_tendsto : ∀ K : Set (Vec d), IsCompact K →
    TendstoUniformlyOn
      (fun L x ↦ SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv
        (SubdiffusiveProcess.Frozen.Assumptions.anchoredPartialSumField omega L) x)
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv g) atTop K
  deriv_lipschitz_cauchy : ∀ K : Set (Vec d), IsCompact K →
    SubdiffusiveProcess.Frozen.Assumptions.LipschitzSeminormCauchyOn
      (fun L x ↦ SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv
        (SubdiffusiveProcess.Frozen.Assumptions.anchoredPartialSumField omega L) x) K
  anchored : g 0 = 0

