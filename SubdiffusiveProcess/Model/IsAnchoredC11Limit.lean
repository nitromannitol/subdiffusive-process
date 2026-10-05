module

public import SubdiffusiveProcess.Assumptions.AnchoredPartialSum

@[expose] public section

/-!
# Anchored local `C¹ˑ¹` convergence
-/

open Filter Homogenization Topology

/-- Values and stored derivatives of the finite anchored sums converge
uniformly on compact sets, while their derivatives are Cauchy in every compact
Lipschitz seminorm. -/
structure SubdiffusiveProcess.Model.IsAnchoredC11Limit {d : ℕ}
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (g : _root_.SubdiffusiveProcess.Model.PotentialField d) : Prop where
  value_tendsto : ∀ K : Set (Vec d), IsCompact K →
    TendstoUniformlyOn
      (fun L x ↦ _root_.SubdiffusiveProcess.Model.anchoredPartialSum omega L x)
      g atTop K
  deriv_tendsto : ∀ K : Set (Vec d), IsCompact K →
    TendstoUniformlyOn
      (fun L x ↦ _root_.SubdiffusiveProcess.Model.PotentialField.deriv
        (_root_.SubdiffusiveProcess.Model.anchoredPartialSumField omega L) x)
      (_root_.SubdiffusiveProcess.Model.PotentialField.deriv g) atTop K
  deriv_lipschitz_cauchy : ∀ K : Set (Vec d), IsCompact K →
    _root_.SubdiffusiveProcess.Model.LipschitzSeminormCauchyOn
      (fun L x ↦ _root_.SubdiffusiveProcess.Model.PotentialField.deriv
        (_root_.SubdiffusiveProcess.Model.anchoredPartialSumField omega L) x) K
  anchored : g 0 = 0
